open Core_kernel.Std open Or_error open OUnit2
open Bap.Std
open Disasm

exception Malformed_input

let create_memory addr s =
  Memory.create LittleEndian Addr.(of_int64 addr) @@
  Bigstring.of_string s |> function
  | Ok r -> r
  | Error err -> print_endline "Internal error: cannot create memory"; exit 1

let kinds_printer insn =
  let output = Insn.kinds insn 
               |> List.map ~f:(fun kind -> 
                   Sexp.to_string_hum (Insn.Kind.sexp_of_t kind))
               |> String.concat ~sep:", " in
  printf "%-8s;%s\n" " " output

let insn_printer insn reg_format imm_format =
  let open Op in
  let init = Sexp.Atom (Insn.name insn) :: [] in
  let res = 
    Insn.ops insn
    |> Array.fold ~init ~f:(fun l x -> match x with
        | Reg reg -> 
          if String.(reg_format = "code") then
            Sexp.Atom ("reg:" ^ Int.to_string (Reg.code reg)) :: l else
            Sexp.Atom (Reg.name reg) :: l
        | Imm imm -> 
          if String.(imm_format = "hex") then
            let v = match Imm.to_int imm with (* XXX to_int? *)
              | Some x -> x
              | None -> print_endline "Could not convert imm value to int!\n"; 
                exit 1 in
            Sexp.Atom (Printf.sprintf "0x%x" v) :: l else
            Sexp.Atom (Imm.to_string imm) :: l
        | Fmm fmm -> 
          Sexp.Atom (Fmm.to_string fmm) :: l) in
  printf "%-8s%-50s" " " @@ Sexp.to_string @@ Sexp.List (List.rev res)

(* Note: Insn.asm returns string with 8 character padding, I'm stripping it 
   so I can add the nice ';' and to keep things consistent *)
let asm_printer insn print_inst=
  let s = String.strip @@ Insn.asm insn in
  if print_inst then
    printf "%-8s; %s" " " s
  else
    printf "%-8s%s" " " s

let print_disasm print_asm print_inst print_kinds reg_format imm_format 
    state mem insn disasm =
  if print_kinds then kinds_printer insn;
  if print_inst then insn_printer insn reg_format imm_format;
  if print_asm then asm_printer insn print_inst;
  (* XXX sigh... *)
  if (print_asm || print_asm || print_inst || print_kinds) then
    printf "\n";
  Basic.step state ()

(* Convert strings to binary representation "\x01\x02..." *)
let to_bin_str s f = 
  try
    String.split ~on:' ' s |> List.map ~f |> String.concat |> Scanf.unescaped
  with Scanf.Scan_failure e -> print_endline "Malformed input"; exit 1  
(* XXX raise Malformed_input *)

let disasm stream arch print_asm print_inst print_kinds reg_format imm_format = 
  let input_src = 
    match stream with
    | "" -> In_channel.input_line In_channel.stdin
    | _ -> Some stream in
  Disasm.Basic.create ~backend:"llvm" arch >>= fun dis ->
  let input = match input_src with
    | Some input ->
      begin match String.prefix input 2 with 
        | "" | "\n" -> exit 0
        | "\\x" -> let f = ident in to_bin_str input f
        | "0x" -> let f = String.substr_replace_all ~pattern:"0x" ~with_:"\\x"
          in to_bin_str input f
        | _ -> let f x = "\\x" ^ x in to_bin_str input f
      end
    | None -> printf "Could not read from stdin"; exit 1 in
  let input_wrapper = create_memory 0x0L input in
  let hit = print_disasm print_asm print_inst print_kinds reg_format 
      imm_format in
  Disasm.Basic.run dis ~return:ident ~stop_on:[`valid] 
    ~hit ~init:() input_wrapper; return ()

open Cmdliner

let arch_opt = 
  let doc = "Target architecture." in
  Arg.(value & opt string "x86_64" & info ["arch"] ~docv:"ARCH" ~doc)

let reg_format_opt =
  let doc = "Register format." in
  Arg.(value & opt string "code" & info ["reg-format"] ~docv:"REG_FORMAT" ~doc)

let imm_format_opt =
  let doc = "Imm format." in
  Arg.(value & opt string "dec" & info ["imm-format"] ~docv:"IMM_FORMAT" ~doc)

let kinds_opt =
  let doc = "Output instruction kinds." in
  Arg.(value & flag & info ["show-kinds"] ~doc)

let inst_opt =
  let doc = "Output list-like disassembly." in
  Arg.(value & flag & info ["show-inst"] ~ doc)

let asm_opt =
  let doc = "Output disassembly." in
  Arg.(value & flag & info ["show-asm"] ~doc)

let stream =
  let doc = "Stream to disassemble (if not specified on stdin)" in
  Arg.(value & pos 0 string "" & info [] ~docv:"STREAM" ~doc)

let cmd =
  let doc = "Disassemble stream" in
  let man = [
    `S "Description";]
  in
  Term.(pure disasm $ stream $ arch_opt $ asm_opt $ inst_opt $ kinds_opt 
          $ reg_format_opt $ imm_format_opt),
  Term.info "dis" ~version:"XX.XX" ~doc ~man

let () = 
  Plugins.load (); 
  let err = Format.std_formatter in
  match Term.eval cmd ~catch:false ~err with
  | `Error _ -> exit 1 
  | _ -> exit 0
