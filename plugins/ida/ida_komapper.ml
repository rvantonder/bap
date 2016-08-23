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

let map_pc_to_dest w relocs =
  let open Option in
  List.find_map relocs ~f:(fun (pc,dest) -> some_if (w = pc) dest)
  >>= fun dest -> return (Bil.int dest)

class bil_ko_symbol_relocator relocs = object(self)
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

let remap_block b memory arch relocs =
  let bil_remapper = new bil_ko_symbol_relocator relocs in
  let arch = Arch.to_string arch in
  (* We need a full_insn type to reconstruct an Insn with an updated
      bil. So re-disassemble from mem to get the full_insn type *)
  Block.insns b |> List.map ~f:(fun (mem,insn) ->
      let bil = Insn.bil insn in
      let bil' = bil_remapper#run bil in
      (*debug_bil_transform bil bil';*)
      match full_insn_of_mem mem arch with
      | Ok (_,Some x,_) -> (mem,Insn.of_basic ~bil:bil' x)
      | _ -> (mem,insn))
  |> Block.create memory

(** Destructs a disassembly block to instruction, transforms the bil
    with relocation information, and reconstructs *)
class remap_cfg relocs arch = object(self)
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

let remap cfg relocs arch =
  let cfg' = cfg in
  let visitor = new remap_cfg relocs arch in
  Graphlib.depth_first_visit (module Graphs.Cfg) cfg ~init:cfg'
    visitor

let clean_extern name proj entry cfg arch =
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



class find_ir_blk_of_addr addr = object(self)
  inherit [Blk.t option] Term.visitor as super

  method! visit_blk blk res =
    let addr_of_blk t = Term.get_attr t Disasm.block in
    match addr_of_blk blk with
    | Some addr' when addr' = addr -> super#visit_blk blk (Some blk)
    | _ -> super#visit_blk blk res
end

let ir_blk_of_addr addr prog =
  let open Option in
  let finder = new find_ir_blk_of_addr addr in
  finder#run prog None >>= fun res ->
  return (Term.tid res)

class jump_table_mapper (relocs : (word * word list) list) prog = object(self)
  inherit Term.mapper as super

  method map_blk blk =
    let open Option in
    super#map_blk blk |> fun blk ->
    let addr_of_jmp jmp = Term.get_attr jmp Disasm.insn_addr in
    let add_jmps =
      Term.to_sequence jmp_t blk |> Seq.fold ~init:[] ~f:(fun acc jmp ->
          List.find_map relocs ~f:(fun (addr,dests) ->
              addr_of_jmp jmp >>= fun addr' ->
              some_if (addr = addr') dests) |> function
          | Some dests ->
            let jumps = List.fold dests ~init:[] ~f:(fun acc addr ->
                (* get the tids of the destination blocks *)
                Option.fold (ir_blk_of_addr addr prog) ~init:acc ~f:(fun acc tid ->
                    (Jmp.create_goto (Direct tid))::acc)) in
            jumps@acc
          | None -> acc) in
    List.fold add_jmps ~init:blk ~f:(fun blk x -> Term.append jmp_t blk x)

end

let map_jump_table relocs prog : program term =
  let relocs = List.filter relocs ~f:(fun (addr,dests) -> List.length dests > 1) in
  let mapper = new jump_table_mapper relocs prog in
  mapper#run prog

let main proj relocs relocs_other =
  let open Option in
  let open Ida_info in
  (* We need a symtab to do Program.lift. Just start with the original symtab *)
  let symtab = Project.symbols proj in
  (* Build a new symtab and just change cfg after mapping >:) *)
  let symtab' =
    Symtab.to_sequence symtab |>
    Seq.fold ~init:(Symtab.empty) ~f:(fun acc (fn_name,fn_start_block,fn_cfg) ->
        (* first, perform relocation *)
        let cfg' = remap fn_cfg relocs (Project.arch proj) in
        (* now make the function clean if it is in .extern *)
        let fn_start,cfg' = clean_extern fn_name proj fn_start_block
            cfg' (Project.arch proj) in
        Symtab.add_symbol acc (fn_name,fn_start_block,cfg')) in
  Program.lift symtab' |> map_jump_table relocs_other |> Project.with_program proj
