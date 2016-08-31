open Core_kernel.Std
open Bap.Std
include Self ()
open Format
open Regular.Std
open Graphlib.Std

(** Bil mapper needs to do something different for .sys:

    00010a1e: calll *0x10a9c
    {
    v94 := mem32[0x10A9C:32, el]:u32
    ESP := ESP - 0x4:32
    mem32 := mem32 with [ESP, el]:u32 <- 0x10A24:32
    jmp v94
    }

    We really want it to just be jmp 0x10A9C to extract the
    correct symbol. Then we'll see

    jmp IofCompleteReq
*)

let map_pc_to_dest w relocs =
  let open Option in
  List.find_map relocs ~f:(fun (pc,dest) -> some_if (w = pc) (dest))
  >>= fun dest -> return (Bil.int dest)


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

let remap_sys_dispatch (bil : bil) =
  let open Option in
  begin
    List.hd bil >>= function
    | Bil.Move (v,Bil.Load (_,e,_,_)) -> return (v,e)
    | _ -> None
  end >>= fun (v,e) ->
  List.rev bil |> List.hd >>= function
  | Bil.Jmp (Bil.Var v') ->
    if Var.name v = Var.name v'
    then match List.rev bil with
      | hd::tl -> (Bil.jmp e)::tl |> List.rev |> return
      | _ -> None
    else None
  | _ -> None

let full_insn_of_mem mem arch =
  Disasm_expert.Basic.with_disasm ~backend:"llvm" arch
    ~f:(fun dis ->
        let open Disasm_expert.Basic in
        let dis = store_kinds dis in
        let dis = store_asm dis in
        insn_of_mem dis mem)

let remap_block b memory arch relocs =
  let arch = Arch.to_string arch in
  (* We need a full_insn type to reconstruct an Insn with an updated
     bil. So re-disassemble from mem to get the full_insn type *)
  Block.insns b |> List.map ~f:(fun (mem,insn) ->
      let bil = Insn.bil insn in
      match remap_sys_dispatch bil with
      | None -> (mem,insn)
      | Some bil' ->
        match full_insn_of_mem mem arch with
        | Ok (_,Some x,_) ->
          printf "Replacement: %a\n" Bil.pp bil';
          (mem,Insn.of_basic ~bil:bil' x)
        | _ -> (mem,insn))
  |> Block.create memory

(** Unused for now *)
let block_of_addr everything addr =
  let enter_node _ blk s =
    match s with
    | Some result -> Some result
    | None ->
      if Block.addr blk = addr then Some blk else None in
  Symtab.to_sequence everything |> Seq.find_map ~f:(fun (_,_,cfg) ->
      Graphlib.depth_first_search (module Graphs.Cfg) cfg ~init:None ~enter_node)

(** Destructs a disassembly block to instruction, transforms the bil
    with relocation information, and reconstructs *)
class remap_cfg everything entry relocs arch = object(self)
  (* types from bap.mli line 4789, Graphs.Cfg. Use the
     identity_visitor so that our class conforms to the dfs_visitor
     type*)
  (* The last type, cfg, which is passed as third argument to
     all methods, is my user state!*)
  inherit [block, Graphs.Cfg.edge, block * cfg] Graphlib.dfs_identity_visitor
  method! enter_node _ b (entry,cfg) =
    let memory = Block.memory b in
    let b' = remap_block b memory arch relocs in
    let ins = Graphs.Cfg.Node.inputs b cfg in
    let outs = Graphs.Cfg.Node.outputs b cfg in
    cfg |> Graphs.Cfg.Node.remove b |> Graphs.Cfg.Node.insert b' |> fun cfg' ->
    Seq.fold ~init:cfg' ins ~f:(Cfg.update_dst b') |> fun cfg' ->
    Seq.fold ~init:cfg' outs ~f:(Cfg.update_src b') |> fun res ->
    if Block.addr b' = Block.addr entry then (b',res)
    else (entry,res)
end

let remap everything entry cfg relocs arch =
  let cfg' = cfg in
  let visitor = new remap_cfg everything entry relocs arch in
  Graphlib.depth_first_visit (module Graphs.Cfg) cfg ~init:(entry,cfg')
    visitor

let clean_extern name proj entry cfg arch =
  let memmap = Project.memory proj in
  Block.memory entry |>
  Memmap.dominators memmap |>
  Seq.find_map ~f:(fun (mem,tag) ->
      match Value.get Image.section tag with
      | Some "extern" | Some "_idata" -> Some mem
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
    let addr_of_blk t = Term.get_attr t address in
    match addr_of_blk blk with
    | Some addr' when addr' = addr -> super#visit_blk blk (Some blk)
    | _ -> super#visit_blk blk res
end

let blk_tid_of_addr addr prog =
  let open Option in
  let finder = new find_ir_blk_of_addr addr in
  finder#run prog None >>= fun res ->
  return (Term.tid res)

(** tid to replace, and what should be placed after it *)
type switch_replacement = (jmp term * jmp term list)

class jump_table_mapper (relocs : (word * word list) list) prog arch =

  (** Get replacements for a given jmp *)
  let replacement_of_jmp jmp acc x = Option.fold x ~init:[] ~f:(fun acc dests ->
      List.foldi dests ~init:acc ~f:(fun i acc addr ->
          (* get the tids of the destination blocks *)
          Option.fold (blk_tid_of_addr addr prog) ~init:acc ~f:(fun acc tid ->
              (** when (~CF) | ZF goto mem [(R3 << 0x2:32) + 0x1390:32 *)
              (** -> when (~CF) | ZF && R3 = 0,1,2,3...i *)
              let cond = Jmp.cond jmp in
              let w = Word.of_int ~width:32 i in
              let r3 = ARM.CPU.r3 in (* XXX arm only *)
              let cond = Bil.(cond land (var r3 = int w)) in
              (Jmp.create_goto ~cond (Direct tid))::acc))) in

  (** Get replacements for a given blk *)
  let replacements_of_blk blk =
    let open Option in
    let addr_of_jmp jmp = Term.get_attr jmp address in
    Term.enum jmp_t blk |> Seq.fold ~init:[] ~f:(fun acc jmp ->
        List.find_map relocs ~f:(fun (addr,dests) ->
            addr_of_jmp jmp >>= fun addr' ->
            some_if (addr = addr') dests) |>
        replacement_of_jmp jmp acc |> fun targets ->
        (jmp,targets)::acc) in

  let replace_jmps_in_blk blk replacements =
    let open Option in
    List.fold replacements ~init:blk ~f:(fun blk (site,add_jmps) ->
        let blk' = List.fold add_jmps ~init:blk ~f:(fun blk jmp ->
            begin
              Term.get_attr site Disasm.insn >>= fun insn ->
              Term.set_attr jmp Disasm.insn insn |> fun jmp' ->
              Term.get_attr site address >>= fun insn_addr ->
              Term.set_attr jmp' address insn_addr |> return
            end |> Option.value ~default:jmp |>
            Term.append ~after:(Term.tid site) jmp_t blk)  in
        (* we must remove the switch jmp after everything has been added after
           site. But only if we added jumps *)
        if List.length add_jmps > 0
        then Term.remove jmp_t blk' (Term.tid site)
        else blk) in

  object(self)
    inherit Term.mapper as super

    method map_blk blk =
      let module Target = (val target_of_arch arch) in (* XXX fix scope *)
      let open ARM in
      let open Option in
      super#map_blk blk |> replacements_of_blk |> replace_jmps_in_blk blk
  end

let map_jump_table relocs arch prog : program term =
  let relocs = List.filter relocs ~f:(fun (addr,dests) -> List.length dests > 1) in
  let mapper = new jump_table_mapper relocs prog arch in
  mapper#run prog

let print_sections p =
  Project.memory p |> Memmap.to_sequence |> Seq.iter ~f:(fun (mem,x) ->
      Option.iter (Value.get Image.section x) ~f:(fun name ->
          printf "Section: %s@.%a@." name Memory.pp mem))

let main proj relocs =
  let open Option in
  let open Ida_info in
  let arch = Project.arch proj in
  print_sections proj;
  (* We need a symtab to do Program.lift. Just start with the original symtab *)
  let symtab = Project.symbols proj in
  (* Build a new symtab and just change cfg after mapping >:) *)
  let symtab' =
    Symtab.to_sequence symtab |>
    Seq.fold ~init:(Symtab.empty) ~f:(fun acc (fn_name,fn_start_block,fn_cfg) ->
        (* first, perform relocation *)
        let fn_start',cfg' =
          remap symtab fn_start_block fn_cfg relocs arch in
        (* now make the function clean if it is in .extern *)
        let _,cfg' = clean_extern fn_name proj fn_start' cfg' arch in
        Symtab.add_symbol acc (fn_name,fn_start',cfg')) in
  Program.lift symtab' |>
  Project.with_program proj
