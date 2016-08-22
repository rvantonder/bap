open Core_kernel.Std
open Bap.Std
include Self ()
open Format
open Regular.Std
open Graphlib.Std

(* DEPRECATED *)
(*
let relocs_of_mem proj =
  let open Option in
  let mem = Project.memory proj in
  Memmap.to_sequence mem |> Seq.fold ~init:[] ~f:(fun acc (mem',tag) ->
      (Value.get comment tag >>= fun s ->
       Memory.min_addr mem' |> fun w ->
       let x = Int.of_string s |> Word.of_int ~width:32 in
       return [(w,x)])
      |> Option.value ~default:[]
      |> fun r -> r@acc)
*)

let map_pc_to_dest w (relocs : (word * word * word list) list) =
  let open Option in
  List.find_map relocs ~f:(fun (pc,dest,_) -> some_if (w = pc) dest)
  >>= fun dest -> return (Bil.int dest)

class bil_ko_symbol_relocator (relocs : (word * word * word list) list) addr =
  object(self)
    inherit Stmt.mapper as super

    (** If there's a BIL jmp with an address to one of our assembly
        addresses, in relocs, it's *probably* jumping to itself, so it
        is a target for relocation. We substitute it with [w], our
        address in the table *)
    method map_jmp e =
      let open Option in
      match e with
      | Bil.Int w ->
        map_pc_to_dest w relocs
        |> Option.value ~default:(Bil.int w)
        |> super#map_jmp
      | _ -> super#map_jmp e
  end

class bil_jump_table_fixup relocs addr = object(self)
  inherit bil_ko_symbol_relocator relocs addr as super

  (** If there's a BIL jump at an address that matches our call site and there
      are multiple and it has multiple destinations, treat it like a switch.
      Assumption: this is called with only one asm insn *)
  method map_stmt s =
    match s with
    | Bil.Move (_,_)
    | Bil.Special _
    | Bil.While (_,_)
    | Bil.If (_,_,_)
    | Bil.CpuExn _ -> super#map_stmt s
    | Bil.Jmp e ->
      let open Option in
      let to_map = List.find_map relocs
          ~f:(fun (callsite,_,dests)
               -> some_if (addr = callsite && List.length dests > 1) dests) in
      match to_map with
      | Some v ->
        let make_addr_switch default_addr addr e =
          let default_dest = Bil.jmp (Bil.int default_addr) in (*XXX*)
          Bil.if_ e [Bil.jmp (Bil.int addr)] [default_dest] in
        List.map v ~f:(fun addr -> make_addr_switch (List.hd_exn v) addr e)
      | None -> super#map_stmt s
end

module Cfg = struct
  include Graphs.Cfg

  (** No edge update method? OK I'll roll my own! *)
  let update_edge cfg e e' = cfg |> Edge.remove e |> Edge.insert e'

  (** use the same label (edge which is `Jump, `Cond, etc) *)
  let update_dst b cfg e =
    let src = Edge.src e in
    let lbl = Edge.label e in
    let e' = Edge.create src b lbl in
    update_edge cfg e e'

  let update_src b cfg e =
    let dst = Edge.dst e in
    let lbl = Edge.label e in
    let e' = Edge.create b dst lbl in
    update_edge cfg e e'
end

let debug_bil_transform bil bil' =
  printf "-------------------------\n%!";
  List.iter bil ~f:(fun b -> printf "%a\n%!" Stmt.pp b);
  List.iter bil' ~f:(fun b -> printf ">> \t%a\n%!" Stmt.pp b);
  printf "-------------------------\n%!"

let full_insn_of_mem mem arch =
  Disasm_expert.Basic.with_disasm ~backend:"llvm" arch
    ~f:(fun dis ->
        let open Disasm_expert.Basic in
        let dis = store_kinds dis in
        let dis = store_asm dis in
        insn_of_mem dis mem)

let remap_block b memory arch (relocs : (word * word * word list) list) =
  let arch = Arch.to_string arch in
  (* We need a full_insn type to reconstruct an Insn with an updated
      bil. So re-disassemble from mem to get the full_insn type *)
  Block.insns b |> List.map ~f:(fun (mem,insn) ->
      let bil = Insn.bil insn in
      let addr = Memory.min_addr mem in
      let bil_remapper = new bil_jump_table_fixup relocs addr in
      let bil' = bil_remapper#run bil in
      (*debug_bil_transform bil bil';*)
      match full_insn_of_mem mem arch with
      | Ok (_,Some x,_) -> (mem,Insn.of_basic ~bil:bil' x)
      | _ -> (mem,insn))
  |> Block.create memory

(** Destructs a disassembly block to instruction, transforms the bil
    with relocation information, and reconstructs *)
class remap_cfg (relocs : (word * word * word list) list) arch = object(self)
  (* types from bap.mli line 4789, Graphs.Cfg. Use the
     identity_visitor so that our class conforms to the dfs_visitor
     type*)
  (* The last type, cfg, which is passed as third argument to
     all methods, is my user state!*)
  inherit [block, Graphs.Cfg.edge, cfg] Graphlib.dfs_identity_visitor
  method! enter_node _ b cfg =
    let memory = Block.memory b in
    let b' = remap_block b memory arch relocs in
    let ins = Graphs.Cfg.Node.inputs b cfg in
    let outs = Graphs.Cfg.Node.outputs b cfg in
    (* we remove the original block, and update the src/dst edges *)
    cfg |> Graphs.Cfg.Node.remove b |> Graphs.Cfg.Node.insert b' |> fun cfg' ->
    Seq.fold ~init:cfg' ins ~f:(Cfg.update_dst b') |> fun cfg' ->
    Seq.fold ~init:cfg' outs ~f:(Cfg.update_src b')
end

(** Jumps to 'self' are replaced by relocated destinations *)
let remap_pc cfg (relocs : (word * word * word list) list) arch =
  let cfg' = cfg in
  let visitor = new remap_cfg relocs arch in
  Graphlib.depth_first_visit (module Graphs.Cfg) cfg ~init:cfg'
    visitor

(** Extern functions (kernel calls) are replaced with an unknown jump
    instruction *)
let clean_extern proj entry cfg arch =
  let memmap = Project.memory proj in
  Block.memory entry |>
  Memmap.dominators memmap |>
  Seq.find_map ~f:(fun (mem,tag) ->
      match Value.get Image.section tag with
      | Some "extern" -> Some mem
      | _ -> None) |> function
  | Some mem ->
    (* I need any instruction in a piece of memory which lifts
       successfully *)
    let s = Bigstring.of_string "\x00\x00\x00\x00" in
    let mem' = match Memory.create LittleEndian (Memory.min_addr mem) s with
      | Ok x -> x
      | _ -> failwith "How could this possibly fail?" in (* XXX *)
    (match full_insn_of_mem mem' (Arch.to_string arch) with
     | Ok (_,Some x,_) ->
       let bil = [Bil.(Jmp (Unknown ("kernel <3", Imm 0)))] in
       let nop_insn = Insn.of_basic ~bil x in
       let nop_block = Block.create mem' [mem',nop_insn] in
       let nop_cfg = Graphs.Cfg.Node.insert nop_block Graphs.Cfg.empty in
       (nop_block,nop_cfg)
     | _ ->
       warning "Failed to disassemble mem. Consider using empty memory";
       entry,cfg)
  | None -> entry,cfg

(* XXX do with IR first? *)
(*class jump_table_mapper_bil = object(self)
  inherit Stmt.mapper

  method map_jmp exp =
  end

  (** Maps *IR* for switch statements. XXX BIL maybe? Complicated...*)
  class jump_table_mapper = object(self)
  inherit Term.mapper as super
  method !map_jmp e = super#map_jmp e
  end

  class remap_jump_tables relocs arch = object (self)
  inherit [block, Graphs.Cfg.edge, cfg] Graphlib.dfs_identity_visitor

  method! enter_node _ block state = state
  end*)

(** Rewrite BIL with jump table information *)
(*let remap_jump_tables cfg proj relocs =
  let cfg' = cfg in
  let visitor = new remap_jump_tables relocs (Project.arch proj) in
  Graphlib.depth_first_visit (module Graphs.Cfg) cfg ~init:cfg' visitor
*)

let main proj (relocs : (word * word * word list) list) =
  let open Option in
  let open Ida_info in
  (* We need a symtab to do Program.lift. Just start with the original symtab *)
  let symtab = Project.symbols proj in
  (* Build a new symtab and just change cfg after mapping >:) *)
  let symtab' =
    Symtab.to_sequence symtab |>
    Seq.fold ~init:(Symtab.empty) ~f:(fun acc (fn_name,fn_start_block,fn_cfg) ->
        (* first, perform relocation *)
        let cfg' = remap_pc fn_cfg relocs (Project.arch proj) in
        (* now make the function clean if it is in .extern *)
        let fn_start,cfg' = clean_extern proj fn_start_block
            cfg' (Project.arch proj) in
        Symtab.add_symbol acc (fn_name,fn_start_block,cfg')) in
  Program.lift symtab' |> Project.with_program proj
