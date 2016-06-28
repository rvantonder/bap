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

let brancher_script =
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
        let branch_of_sexp x = [%of_sexp: (int64 * (int64 * edge) list)] x in
        In_channel.with_file name ~f:(fun ch ->
            Sexp.input_sexps ch |> List.map ~f:branch_of_sexp))

let addr_of_mem mem =
  Memory.min_addr mem
  |> Bitvector.to_int64
  |> function
  | Ok addr -> Some addr
  | Error _ -> None

let resolve_dests memory lookup =
  let open Option in
  addr_of_mem memory >>= fun addr ->
  List.Assoc.find lookup addr >>= fun l ->
  List.map l (fun (x,y) -> (Some (Word.of_int64 x),y))
  |> return

(** Brancher is created with (mem → (asm, kinds) insn →
    (word option * [ `Cond | `Fall | `Jump ]) list) signature *)
let branch_lookup path =
  match Ida.(with_file path brancher_script) with
  | [] ->
    warning "didn't find any branches";
    info "this plugin doesn't work with IDA free";
    (fun mem insn -> [])
  | lookup ->
    (fun mem insn ->
       resolve_dests mem lookup
       |> Option.value ~default:[])

let register_brancher_source () =
  let source =
    let open Project.Info in
    let open Option in
    Stream.merge file arch ~f:(fun file arch ->
        Or_error.try_with (fun () ->
            Brancher.create (branch_lookup file))) in
  Brancher.Factory.register name source

let symbolizer_script =
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
    | None -> match Ida.(with_file path symbolizer_script) with
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

let loader_script =
  {|
    from bap.utils.ida import dump_loader_info
    dump_loader_info('$output')
    idc.Exit(0)
  |}

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

let load_image = Command.create `python
    ~script:loader_script
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
                            (Error.to_string_hum e)
    )
