open Core_kernel.Std
open Regular.Std
open Bap_future.Std
open Bap.Std
open Bap_ida.Std

open Format
open Result.Monad_infix

include Self()

module Symbols = Data.Make(struct
    type t = (string * int64 * int64) list
    let version = "0.1"
  end)

module type Target = sig
  type t
  val of_blocks : (string * addr * addr) seq -> t
  module Factory : sig
    val register : string -> t source -> unit
  end
end

let brancher_command =
  let script =
    {|
from bap.utils.ida import dump_brancher_info
dump_brancher_info('$output')
idc.Exit(0)
|} in
  Command.create
    `python
    ~script
    ~parser:(fun name ->
        let branch_of_sexp x =
          [%of_sexp: int64 * int64 option * int64 list] x in
        In_channel.with_file name ~f:(fun ch ->
            Sexp.input_sexps ch |> List.map ~f:branch_of_sexp))

let brancher_command_test =
  let branch_of_sexp x = [%of_sexp: int64 * int64 option * int64 list] x in
  In_channel.with_file "/tmp/noot" ~f:(fun ch ->
      Sexp.input_sexps ch |> List.map ~f:branch_of_sexp)

(** (addr * (normal flow 0 or 1) (list of "other flows") *)
(** speculate: (Jump (0 or 1)) (Fall or Cond) *)
let branch_lookup_of_file f =
  let branch_of_sexp x = [%of_sexp: int64 * int64 option * int64 list] x in
  In_channel.with_file f ~f:(fun ch ->
      Sexp.input_sexps ch |> List.map ~f:branch_of_sexp)

let print_result mem dests =
  let output x = [%sexp_of: int64 * int64 option * int64 list] x in
  Format.printf "(%a %s)\n%!" Addr.pp (Memory.min_addr mem)
    (Sexp.to_string (output dests))

let default_print_result mem dests =
  let output x = [%sexp_of: (addr option * edge) list] x in
  Format.printf "(%a %s)\n%!" Addr.pp (Memory.min_addr mem)
    (Sexp.to_string (output dests))

let addr_of_mem mem =
  Memory.min_addr mem
  |> Bitvector.to_int64
  |> function
  | Ok addr -> Some addr
  | Error _ -> None

type edge = Bap_disasm_block.edge [@@deriving sexp]
type dest = addr option * edge [@@deriving sexp]
type dests = dest list [@@deriving sexp]
type full_insn = Bap_disasm_basic.full_insn

let kind_of_dests = function
  | xs when List.for_all xs ~f:(fun (_,x) -> x = `Fall) -> `Fall
  | xs -> if List.exists  xs ~f:(fun (_,x) -> x = `Jump)
    then `Jump
    else `Cond

let kind_of_branches t f =
  match kind_of_dests t, kind_of_dests f with
  | `Jump,`Jump -> `Jump
  | `Fall,`Fall -> `Fall
  | _           -> `Cond

let fold_consts = Bil.(fixpoint fold_consts)

let rec dests_of_bil (bil : stmt list) : dests =
  fold_consts bil |> List.concat_map ~f:dests_of_stmt
and dests_of_stmt = function
  | Bil.Jmp (Bil.Int addr) -> [Some addr,`Jump]
  | Bil.Jmp (_) -> [None, `Jump]
  | Bil.If (_,yes,no) -> merge_branches yes no
  | Bil.While (_,ss) -> dests_of_bil ss
  | _ -> []
and merge_branches yes no =
  let x = dests_of_bil yes and y = dests_of_bil no in
  let kind = kind_of_branches x y in
  List.(rev_append x y >>| fun (a,_) -> a,kind)

(* addr option * edge list *)
let print_result mem dests =
  let output x = [%sexp_of: (addr option * edge) list] x in
  Format.printf "(%a %s)\n%!" Addr.pp (Memory.min_addr mem)
    (Sexp.to_string (output dests))

let resolve_dests memory insn lookup =
  let open Option in
  let (!) = Word.of_int64 ~width:32 in
  addr_of_mem memory >>= fun needle ->
  List.find lookup ~f:(fun (addr,_,_) -> needle = addr) >>=
  (* dests is addr option * edge list *)
  fun (_,opt,rest) ->
  (match opt with
   | Some fall ->
     printf
       "Addr: %a. Dest looks like a fallthrough edge: %a\n%!"
       Addr.pp !needle Addr.pp !fall;
   | None -> ());
  return [Some (Word.of_int64 ~width:32 needle),`Jump]

(** Brancher is created with (mem → (asm, kinds) insn →
    (word option * [ `Cond | `Fall | `Jump ]) list) signature *)
let branch_lookup arch path =
  let open Bil in
  let module Target = (val target_of_arch arch) in
  let lookup = branch_lookup_of_file "/tmp/noot" in
  (*match Ida.(with_file path brancher_command) with*) (* XXX *)
  match lookup with
  | [] ->
    warning "didn't find any branches";
    info "this plugin doesn't work with IDA free";
    fun mem insn -> []
  | lookup ->
    fun mem insn ->
      match resolve_dests mem insn lookup with
      | None -> []
      | Some dests -> dests

let default_branch_lookup arch path =
  let open Bil in
  let module Target = (val target_of_arch arch) in
  match Ida.(with_file path brancher_command) with
  (*match brancher_command_test with*)
  | [] ->
    warning "didn't find any branches";
    info "this plugin doesn't work with IDA free";
    fun mem insn -> []
  | lookup ->
    fun mem insn ->
      let next = Addr.succ (Memory.max_addr mem) in
      (** This this instruction. Use the bil to extract the
          destinations *)
      let dests = match Target.lift mem insn with
        | Error _ -> []
        | Ok bil -> dests_of_bil bil in
      let is = Disasm_expert.Basic.Insn.is insn in
      let fall = Some next, `Fall in
      let result =
        match kind_of_dests dests with
        | `Fall when is `Return -> []
        | `Jump when is `Call -> fall :: dests
        | `Cond | `Fall -> fall :: dests
        | _ -> dests in
      default_print_result mem result;
      result

let register_brancher_source () =
  let source =
    let open Project.Info in
    let open Option in
    Stream.merge file arch ~f:(fun file arch ->
        (*let default_brancher = Bap_disasm_brancher.of_bil arch in*)
        Or_error.try_with (fun () ->
            Brancher.create (branch_lookup arch file)
          )) in
  Brancher.Factory.register name source

let symbolizer_command =
  let script =
    {|
from bap.utils.ida import dump_symbol_info
dump_symbol_info('$output')
idc.Exit(0)
|} in
  Command.create
    `python
    ~script
    ~parser:(fun name ->
        let blk_of_sexp x = [%of_sexp:string*int64*int64] x in
        In_channel.with_file name ~f:(fun ch ->
            Sexp.input_sexps ch |> List.map ~f:blk_of_sexp))

let extract path arch =
  let id =
    Data.Cache.digest ~namespace:"ida" "%s" (Digest.file path) in
  let syms = match Symbols.Cache.load id with
    | Some syms -> syms
    | None -> match Ida.(with_file path symbolizer_command) with
      | [] ->
        warning "didn't find any symbols";
        info "this plugin doesn't work with IDA Free";
        []
      | syms -> Symbols.Cache.save id syms; syms in
  let size = Arch.addr_size arch in
  let width = Size.in_bits size in
  let addr = Addr.of_int64 ~width in
  List.map syms ~f:(fun (n,s,e) -> n, addr s, addr e) |>
  Seq.of_list

let register_source (module T : Target) =
  let source =
    let open Project.Info in
    let extract file arch = Or_error.try_with (fun () ->
        (* of_blocks takes string addr addr seq *)
        (* produces a factory source *)
        extract file arch |> T.of_blocks) in
    Stream.merge file arch ~f:extract in
  T.Factory.register name source

type perm = [`code | `data] [@@deriving sexp]
type section = string * perm * int * (int64 * int)
  [@@deriving sexp]

type image = string * addr_size * section list [@@deriving sexp]

module Img = Data.Make(struct
    type t = image
    let version = "0.1"
  end)


exception Unsupported_architecture of string

let arch_of_procname size name = match String.lowercase name with
  | "8086" | "80286r" | "80286p"
  | "80386r" | "80386p"
  | "80486r" | "80486p"
  | "80586r" | "80586p"
  | "80686p" | "k62" | "p2" | "p3" | "athlon" | "p4" | "metapc" ->
    if size = `r32 then `x86 else `x86_64
  | "ppc" ->  if size = `r64 then `ppc64 else `ppc
  | "ppcl" ->  `ppc64
  | "arm" ->  `armv7
  | "armb" ->  `armv7eb
  | "mipsl" ->  if size = `r64 then `mips64el else `mipsel
  | "mipsb" ->  if size = `r64 then `mips64  else `mips
  | "sparcb" -> if size = `r64 then `sparcv9 else `sparc
  | s -> raise (Unsupported_architecture s)

let read_image name =
  In_channel.with_file name ~f:(fun ch ->
      Sexp.input_sexp ch |> image_of_sexp)

let load_image =
  let script =
    {|
from bap.utils.ida import dump_loader_info
dump_loader_info('$output')
idc.Exit(0)
|} in
  Command.create `python
    ~script
    ~parser:read_image

let mapfile path : Bigstring.t =
  let fd = Unix.(openfile path [O_RDONLY] 0o400) in
  let size = Unix.((fstat fd).st_size) in
  let data = Bigstring.map_file ~shared:false fd size in
  Unix.close fd;
  data

let loader path =
  let id = Data.Cache.digest ~namespace:"ida-loader" "%s"
      (Digest.file path) in
  let (proc,size,sections) = match Img.Cache.load id with
    | Some img -> img
    | None ->
      let img = Ida.with_file path load_image in
      Img.Cache.save id img;
      img in
  let bits = mapfile path in
  let arch = arch_of_procname size proc in
  let endian = Arch.endian arch in
  let addr = Addr.of_int64 ~width:(Size.in_bits size) in
  let code,data = List.fold sections
      ~init:(Memmap.empty,Memmap.empty)
      ~f:(fun (code,data) (name,perm,pos,(beg,len)) ->
          let mem_or_error =
            (** either match pos against or -1 or name against "extern" *)
            match pos with
            | -1 ->
              info "Creating synthetic IDA section %s" name;
              Memory.create ~pos:0 endian (addr beg) bits
            | _ -> Memory.create ~pos ~len endian (addr beg) bits in
          match mem_or_error with
          | Error err ->
            info "skipping section %s: %a" name Error.pp err;
            code,data
          | Ok mem ->
            let sec = Value.create Image.section name in
            if perm = `code
            then Memmap.add code mem sec, data
            else code, Memmap.add data mem sec) in
  Project.Input.create arch path ~code ~data

let require req check =
  if check
  then Ok ()
  else Or_error.errorf "IDA configuration failure: %s" req

let checked ida_path is_headless =
  let (/) = Filename.concat in
  require "path must exist"
    (Sys.file_exists ida_path) >>= fun () ->
  require "path must be a folder"
    (Sys.is_directory ida_path) >>= fun () ->
  require "can't use headless on windows"
    (is_headless ==> not Sys.win32) >>= fun () ->
  require "idaq must exist"
    (Sys.file_exists (ida_path/"idaq")) >>= fun () ->
  require "idaq64 must exist"
    (Sys.file_exists (ida_path/"idaq64")) >>= fun () ->
  require "idal must exist"
    (Sys.file_exists (ida_path/"idal")) >>= fun () ->
  require "idal64 must exist"
    (Sys.file_exists (ida_path/"idal64")) >>= fun () ->
  require "bap-ida-python must be installed"
    (Sys.file_exists
       (ida_path/"plugins"/"plugin_loader_bap.py"))  >>| fun () ->
  ida_path


let main () =
  register_source (module Rooter);
  register_source (module Symbolizer);
  register_source (module Reconstructor);
  register_brancher_source ();
  Project.Input.register_loader name loader

let () =
  let () = Config.manpage [
      `S "DESCRIPTION";
      `P "This plugin provides rooter, symbolizer and reconstuctor services.";
      `P "If IDA instance is found on the machine, or specified by a
   user, it will be queried for the specified information."
    ] in
  let path =
    let doc = "Path to IDA directory." in
    Config.(param string "path" ~default:Bap_ida_config.ida_path ~doc) in
  let headless =
    let doc = "Use headless curses based IDA." in
    Config.(param bool "headless" ~default:Bap_ida_config.is_headless ~doc) in
  Config.when_ready (fun {Config.get=(!)} ->
      match checked !path !headless with
      | Result.Ok path -> Bap_ida_service.register path !headless; main ()
      | Result.Error e -> error "%S. Service not registered."
                            (Error.to_string_hum e))
