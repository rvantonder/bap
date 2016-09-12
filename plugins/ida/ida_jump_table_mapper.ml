open Core_kernel.Std
open Bap.Std
include Self ()

(** tid to replace, and what should be placed after it *)
type switch_replacement = (jmp term * jmp term list)

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

(**
   Currently incorrect. usbcore.ko example:

   0000b71b:
   0x1378:32: 0000b71c: v18883 := mem[R5, el]:u8
   0x1378:32: 0000b71d: R3 := pad:32[v18883]
   0x1378:32: 0000b71e: R5 := R5 + 0x1:32
   0x137C:32: 0000b71f: R4 := R4 + 0x1:32
   0x1380:32: 0000b720: R3 := R3 - 0x1:32
   0x1384:32: 0000b721: CF := 0x6:32 <= R3
   0x1384:32: 0000b722: VF := high:1[(R3 ^ 0x6:32) & (R3 ^ (R3 - 0x6:32))]
   0x1384:32: 0000b723: NF := high:1[R3 - 0x6:32]
   0x1384:32: 0000b724: ZF := (R3 - 0x6:32) = 0x0:32
   0x1388:32: 00015382: when ((~CF) | ZF) & (R3 = 0x0:32) goto %0000b72c
   0x1388:32: 00015383: when ((~CF) | ZF) & (R3 = 0x1:32) goto %0000b734
   0x1388:32: 00015384: when ((~CF) | ZF) & (R3 = 0x2:32) goto %0000b727
   0x1388:32: 00015385: when ((~CF) | ZF) & (R3 = 0x3:32) goto %0000b740
   0x1388:32: 00015386: when ((~CF) | ZF) & (R3 = 0x4:32) goto %0000b73c
   0x1388:32: 00015387: when ((~CF) | ZF) & (R3 = 0x5:32) goto %0000b730
   0x1388:32: 00015388: when ((~CF) | ZF) & (R3 = 0x6:32) goto %0000b738
   0000b726: goto %0000b750

   R3 values do not match IDA cases. That's because the ARM compiler is doing
   funny things for making the jump table:

   .text:00001384                 CMP             R3, #6  ; switch 7 cases
   .text:00001388                 LDRLS           PC, [PC,R3,LSL#2] ; switch jump
   .text:0000138C                 B               loc_13CC ; jumptable 00001388
   default case
   .text:0000138C ;
   ---------------------------------------------------------------------------
   .text:00001390                 DCD loc_142C            ; jump table
   .text:00001394                 DCD loc_1420
   .text:00001398                 DCD loc_1414
   .text:0000139c                 DCD loc_1408
   .text:000013a0                 DCD loc_13FC
   .text:000013a4                 DCD loc_13AC
   .text:000013a8                 DCD loc_13F0
   .text:000013AC ;
   ---------------------------------------------------------------------------
   .text:000013AC

   Notice how the jump destinations are not in order of addresses. So the right
   way to do this would be to perform the left shift, and dereference the
   address at that position to get the right pointer for each case.
*)

class jump_table_mapper (relocs : (word * word list) list) prog arch =
  let get_replacement_jmps jmp acc x = Option.fold x ~init:[] ~f:(fun acc dests ->
      List.foldi dests ~init:acc ~f:(fun i acc addr ->
          (* get the tids of the destination blocks *)
          Option.fold (blk_tid_of_addr addr prog) ~init:acc ~f:(fun acc tid ->
              let cond = Jmp.cond jmp in
              let w = Word.of_int ~width:32 i in
              let r3 = ARM.CPU.r3 in (* XXX ARM specific *)
              let cond = Bil.(cond land (var r3 = int w)) in
              (Jmp.create_goto ~cond (Direct tid))::acc))) in
  object(self)
    inherit Term.mapper as super

    method map_blk blk =
      let module Target = (val target_of_arch arch) in
      let open ARM in
      let open Option in
      super#map_blk blk |> fun blk ->
      let addr_of_jmp jmp = Term.get_attr jmp address in
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
                  Term.get_attr site address >>= fun insn_addr ->
                  Term.set_attr x' address insn_addr |> return
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

let main proj relocs_other =
  let arch = Project.arch proj in
  match arch with
  | #Arch.arm ->
    Project.program proj |>
    map_jump_table relocs_other (Project.arch proj) |>
    Project.with_program proj
  | _ ->
    info "Skipping pass: Ida_jump_table_mapper. It currently only supports ARM";
    proj
