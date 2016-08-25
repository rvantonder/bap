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
  List.find_map relocs ~f:(fun (pc,dest) -> some_if (w = pc) (pc,dest))
  >>= fun (pc,dest) ->
  printf "PC %a will remap to %a@." Word.pp pc Word.pp dest;
  return (Bil.int dest)

class bil_ko_symbol_relocator relocs = object(self)
  inherit Stmt.mapper as super

  (** If there's a BIL jmp with an address to one of our assembly
      addresses, in relocs, it's *probably* jumping to itself, so it
      is a target for relocation. We substitute it with [w], our
      address in the table *)
  (** Problem: there's a BIL jmp to destination 0x2380 which is a fallthrough,
      and it's not getting picked up here. we should substitute it with that
      fallthrough dest. But what to do since there can be multiple dests? How
      do we know it should be the fallthrough and not a conditional? Do
      conditionals first, then fallthroughs, and cross fingers? *)
  method map_jmp e =
    let open Option in
    match e with
    | Bil.Int w ->
      map_pc_to_dest w relocs
      |> Option.value ~default:(Bil.int w)
      |> fun res ->
      printf "Bil jmp remap: %a -> %a" Exp.pp e Exp.pp res;
      super#map_jmp res
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
      | Ok (_,Some x,_) ->
        printf "Success! REplacement: %a\n" Bil.pp bil';
        (mem,Insn.of_basic ~bil:bil' x)
      | _ ->
        printf "Failed for mem with addr %a\n" Word.pp @@ Memory.min_addr mem;
        (mem,insn))
  |> Block.create memory

let debug_edges ins outs b =
  printf "==========================================@.";
  Seq.iter ins ~f:(fun _in ->
      printf "In: %a@." Block.pp @@ Graphs.Cfg.Edge.src _in);
  Seq.iter outs ~f:(fun _out ->
      printf "Out: %a@." Block.pp @@ Graphs.Cfg.Edge.dst _out);
  printf "For Block %a@." Block.pp b;
  printf "==========================================@."

let block_of_addr everything addr =
  let enter_node _ blk s =
    match s with
    | Some result -> Some result
    | None ->
      if Block.addr blk = addr then Some blk else None in
  Symtab.to_sequence everything |> Seq.find_map ~f:(fun (_,_,cfg) ->
      Graphlib.depth_first_search (module Graphs.Cfg) cfg ~init:None ~enter_node)

let print_block block =
  printf "%a" Block.pp block;
  Block.insns block |> List.iter ~f:(fun (m,i) ->
      printf "%a@." Bil.pp @@ Insn.bil i);
  printf "@."

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
    (*printf "@.@. ENTER @.@.";*)
    let (!) = Word.of_int ~width:32 in
    let memory = Block.memory b in
    let b' = remap_block b memory arch relocs in
    let ins = Graphs.Cfg.Node.inputs b cfg in
    let outs = Graphs.Cfg.Node.outputs b cfg in
    (*let outs =
      if Block.addr b = !0x2370 then
        begin
          printf "Trying baby";
          match block_of_addr everything !0x2380 with
          | Some dest ->
            printf "Creating that fake edge";
            (Graphs.Cfg.Edge.create b dest `Fall)^::outs
          | None -> outs end
      else outs in*)
    (*debug_edges ins outs b;
      printf "Removing\n";
      print_block b;
      printf "Inserting\n";
      print_block b';
      printf "@.@. EXIT @.@.";*)
    (* we remove the original block, and update the src/dst edges *)
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

let blk_tid_of_addr addr prog =
  let open Option in
  let finder = new find_ir_blk_of_addr addr in
  finder#run prog None >>= fun res ->
  return (Term.tid res)

(** tid to replace, and what should be placed after it *)
type switch_replacement = (jmp term * jmp term list)

class jump_table_mapper (relocs : (word * word list) list) prog arch =
  let get_replacement_jmps jmp acc x = Option.fold x ~init:[] ~f:(fun acc dests ->
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
  object(self)
    inherit Term.mapper as super

    method map_blk blk =
      let module Target = (val target_of_arch arch) in (* XXX fix scope *)
      let open ARM in
      let open Option in
      super#map_blk blk |> fun blk ->
      let addr_of_jmp jmp = Term.get_attr jmp Disasm.insn_addr in
      let res : switch_replacement list =
        Term.enum jmp_t blk |> Seq.fold ~init:[] ~f:(fun acc jmp ->
            List.find_map relocs ~f:(fun (addr,dests) ->
                addr_of_jmp jmp >>= fun addr' ->
                some_if (addr = addr') dests) |>
            get_replacement_jmps jmp acc |> fun targets ->
            (jmp,targets)::acc) in
      List.fold res ~init:blk ~f:(fun blk (site,add_jmps) ->
          let blk' =
            List.fold add_jmps ~init:blk ~f:(fun blk x ->
                begin
                  Term.get_attr site Disasm.insn >>= fun insn ->
                  Term.set_attr x Disasm.insn insn |> fun x' ->
                  Term.get_attr site Disasm.insn_addr >>= fun insn_addr ->
                  Term.set_attr x' Disasm.insn_addr insn_addr |> return
                end |> Option.value ~default:x |>
                Term.append ~after:(Term.tid site) jmp_t blk
              ) in
          (* must remove after everything has been added after site. But only
             if we added jumps *)
          if List.length add_jmps > 0
          then Term.remove jmp_t blk' (Term.tid site)
          else blk)
  end

let map_jump_table relocs arch prog : program term =
  let relocs = List.filter relocs ~f:(fun (addr,dests) -> List.length dests > 1) in
  let mapper = new jump_table_mapper relocs prog arch in
  mapper#run prog

let print_sections proj =
  Project.memory proj |> Memmap.to_sequence |> Seq.iter ~f:(fun (mem,x) ->
      Option.iter (Value.get Image.section x) ~f:(fun name ->
          printf "Section: %s@.%a@." name Memory.pp mem))

let print_symbols proj =
  Project.symbols proj |> Symtab.to_sequence |> Seq.iter ~f:(fun (name,_,_) ->
      printf "%s\n" name)

let main proj relocs relocs_other =
  let open Option in
  let open Ida_info in
  (*print_sections proj;*)
  print_symbols proj;
  (* We need a symtab to do Program.lift. Just start with the original symtab *)
  let symtab = Project.symbols proj in
  (* Build a new symtab and just change cfg after mapping >:) *)
  let symtab' =
    Symtab.to_sequence symtab |>
    Seq.fold ~init:(Symtab.empty) ~f:(fun acc (fn_name,fn_start_block,fn_cfg) ->
        (* first, perform relocation *)
        let fn_start',cfg' = remap symtab fn_start_block fn_cfg relocs (Project.arch proj) in
        (* now make the function clean if it is in .extern *)
        let fn_start',cfg' = clean_extern fn_name proj fn_start'
            cfg' (Project.arch proj) in
        printf "@. What we expect for %s? @." fn_name;
        print_block fn_start_block;
        printf "@. /End @.";
        Symtab.add_symbol acc (fn_name,fn_start',cfg')) in
  Program.lift symtab' |>
  map_jump_table relocs_other (Project.arch proj) |>
  Project.with_program proj

(** Problem is: bil is updated in entry block, but we dont' update the
    entry itself. when it builds, it uses that block and the fucking edges,
    so our change gets lost *)
