open Core_kernel.Std
open Regular.Std
open Bap_future.Std
open Bap.Std
open Bap_ida.Std

open Format
open Result.Monad_infix

open Ida_info
open Ida_commands

include Self()

module Ida_futures = struct
  type ('a,'b,'c) t =
    {symbols : 'a future * 'a promise;
     brancher : 'b future * 'b promise;
     img : 'c future * 'c promise} [@@ deriving fields]
end

open Ida_futures

let read_future future =
  match Future.peek future with
  | Some v -> v
  | None -> failwith "Using futures failed: no value!\n"

module type Target = sig
  type t
  val of_blocks : (string * addr * addr) seq -> t
  module Factory : sig
    val register : string -> t source -> unit
  end
end

let addr_of_mem mem =
  Memory.min_addr mem
  |> Bitvector.to_int64
  |> function
  | Ok addr -> Some addr
  | Error _ -> None

let handle_normal_flow =
  let (!) = Word.of_int64 ~width:32 in
  function
  | Some fall -> [Some !fall, `Fall]
  | None -> []

(** We have to figure out what the kind is of the other jumps. We use
    the default Bil brancher: if it has a destination that matches one of
    ours, then we just use that edge type. If not, we just use jump *)
let handle_other_flow default rest =
  let (!) = Word.of_int64 ~width:32 in
  match rest with
  | [] -> []
  | l ->
    List.fold l ~init:[] ~f:(fun acc dest_addr ->
        match List.find default ~f:(fun (addr,_) -> addr = Some !dest_addr) with
        (* If the IDA dest addr is in the default BIL brancher, use same edge *)
        | Some (Some addr,kind) -> (Some !dest_addr, kind)::acc
        (* XXX heuristic: we are assuming `Jump always (when it could be cond) *)
        | _ -> (Some !dest_addr, `Jump)::acc)

(** Given a piece of memory and an insn, return a list of destination
    addrs, and the kind of edge, from this insn. Format:
    (addr option * [ `Cond | `Fall | `Jump ]) list *)
let resolve_dests memory insn lookup arch =
  let open Option in
  let module Target = (val target_of_arch arch) in
  addr_of_mem memory >>= fun addr ->
  (* Only process further if this addr is in our lookup: i.e. we know
     that we have branch information for it. *)
  List.find lookup ~f:(fun (needle,_,_) -> needle = addr) >>=
  (* provide the default information to help with other_flow *)
  let default_brancher = Brancher.of_bil arch in
  let default = Brancher.resolve default_brancher memory insn
  in
  fun (_,opt,(rest : int64 list)) ->
    let normal_flow = handle_normal_flow opt in
    let other_flow = handle_other_flow default rest in
    other_flow@normal_flow |> return

(** Brancher is created with (mem → (asm, kinds) insn →
    (word option * [ `Cond | `Fall | `Jump ]) list) signature *)
let branch_lookup futures arch path =
  let open Bil in
  (*let lookup = Ida.with_file path brancher_command in*)
  let id = Data.Cache.digest ~namespace:"ida-brancher"
      "%s" (Digest.file path) in
  let lookup = match Brancher_info.Cache.load id with
    | Some lookup -> lookup
    | None ->
      info "No caching enabled, using futures!";
      read_future (fst futures.brancher)
  in
  match lookup with
  | [] ->
    warning "didn't find any branches";
    info "this plugin doesn't work with IDA free";
    fun mem insn -> []
  | lookup -> fun mem insn ->
    match resolve_dests mem insn lookup arch with
    | None -> []
    | Some dests -> dests

let register_brancher_source streams =
  let source =
    let open Project.Info in
    let open Option in
    Stream.merge file arch ~f:(fun file arch ->
        Or_error.try_with (fun () ->
            Brancher.create (branch_lookup streams arch file))) in
  Brancher.Factory.register name source

let extract futures path arch =
  let id = Data.Cache.digest ~namespace:"ida" "%s" (Digest.file path) in
  let syms = match Symbols.Cache.load id with
    | Some syms -> syms
    | None ->
      info "No caching enabled, using streams!";
      read_future (fst futures.symbols) in
  let size = Arch.addr_size arch in
  let width = Size.in_bits size in
  let addr = Addr.of_int64 ~width in
  let res =
    List.map syms ~f:(fun (n,s,e) -> n, addr s, addr e) in
  Seq.of_list res

let register_source streams (module T : Target) =
  let source =
    let extract file arch = Or_error.try_with (fun () ->
        extract streams file arch |> T.of_blocks) in
    Stream.merge Project.Info.file Project.Info.arch ~f:extract in
  T.Factory.register name source

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

let mapfile path : Bigstring.t =
  let fd = Unix.(openfile path [O_RDONLY] 0o400) in
  let size = Unix.((fstat fd).st_size) in
  let data = Bigstring.map_file ~shared:false fd size in
  Unix.close fd;
  data

let get_relocs lookup =
  let (!) = Word.of_int64 ~width:32 in
  List.fold ~init:[] lookup ~f:(fun acc (addr,_,l) ->
      match List.hd l with
      | Some dest -> (!addr,!dest)::acc
      | None -> acc)

let get_relocs_other lookup =
  let (!) = Word.of_int64 ~width:32 in
  List.fold ~init:[] lookup ~f:(fun acc (addr,_,l) ->
      match List.hd l with
      | Some dest -> (!addr,List.map ~f:(!) l)::acc
      | None -> acc)

(* XXX only for arm *)
let tag_branches_of_mem_extern memmap path lookup =
  let (!) = Word.of_int64 ~width:32 in
  let (!@) x =
    let open Or_error in
    match x with
    | Ok x -> Some x
    | Error _ -> None in
  let open Option in
  Memmap.to_sequence memmap
  |> Seq.fold ~init:memmap ~f:(fun memmap' (mem,x) ->
      List.fold ~init:memmap' lookup ~f:(fun memmap_inner (addr,_,l) ->
          (!@(Memory.view ~word_size:`r8 ~from:!addr ~words:4 mem)
           >>= fun mem' -> List.hd l >>= fun dest ->
           Memmap.add memmap_inner mem'
             (Value.create comment (Int64.to_string dest)) |> return)
          |> Option.value ~default:memmap_inner))

let create_mem pos len endian beg bits size =
  let addr = Addr.of_int64 ~width:(Size.in_bits size) in
  (* For synthetic regions, either match pos against or -1 or name
      against "extern" *)
  match pos with
  | -1 ->
    info "Creating synthetic IDA section %S with len %d" name len;
    (* XXX make space for elf header *)
    Memory.create ~pos:0 ~len endian (addr Int64.(beg - Int64.of_int 0x4)) bits
  | _ -> Memory.create ~pos ~len endian (addr beg) bits

(** If caching is off, we will always send the info to the future *)
let preload_ida_info path (futures : ('a,'b,'c) Ida_futures.t) =
  let preload ~namespace (type t) (module M : Data with type t = t)
      command field =
    let id = Data.Cache.digest ~namespace "%s" (Digest.file path) in
    match M.Cache.load id with
    | Some _ -> ()
    | None ->
      let data = Ida.with_file path command in
      M.Cache.save id data;
      Promise.fulfill (snd (Field.get field futures)) data in

  Ida_futures.Fields.iter
    ~img:(preload ~namespace:"ida-loader" (module Img) load_image)
    ~symbols:(preload ~namespace:"ida" (module Symbols) symbolizer_command)
    ~brancher:(preload ~namespace:"ida-brancher"
                 (module Brancher_info) brancher_command)

let loader got_path (futures : ('a,'b,'c) Ida_futures.t) path =
  Promise.fulfill got_path path;
  preload_ida_info path futures;
  let id = Data.Cache.digest ~namespace:"ida-loader" "%s" (Digest.file path) in
  let (proc,size,sections) =
    match Img.Cache.load id with
    | Some img -> img
    | None ->
      info "No caching enabled, using streams!";
      read_future (fst futures.img) in
  let id = Data.Cache.digest ~namespace:"ida-brancher" "%s" (Digest.file path) in
  let lookup =
    match Brancher_info.Cache.load id with (*XXX make generic lookup routine*)
    | Some img -> img
    | None ->
      info "No caching enabled, using streams!";
      read_future (fst futures.brancher)
  in
  let bits = mapfile path in
  let arch = arch_of_procname size proc in
  let endian = Arch.endian arch in
  let code,data = List.fold sections
      ~init:(Memmap.empty,Memmap.empty)
      ~f:(fun (code,data) (name,perm,pos,(beg,len)) ->
          info "Processing section %S" name;
          let mem_or_error = create_mem pos len endian beg bits size in
          match mem_or_error with
          | Error err ->
            info "skipping section %s: %a" name Error.pp err;
            code,data
          | Ok mem ->
            let sec = Value.create Image.section name in
            match perm,name with
            | `code,_ -> Memmap.add code mem sec, data
            | _,"extern" (* linux .ko modules *)
            | _,"_idata" -> (* windows .sys drivers *)
              info "Handling _idata section";
              (* Add "extern" mem to code memmap *)
              let code' = Memmap.add code mem sec in
              (* annotate insns that branch to extern *)
              let code' = tag_branches_of_mem_extern code' path lookup in
              code',data
            | _ -> code, Memmap.add data mem sec) in
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
  (* path is here so that we can pass the filename. we need to cache
     it there too in case the loader gets cached. I've seen it happen.*)
  let path,got_path = Future.create () in
  let ida_symbols_info,got_ida_symbols_info = Future.create () in
  let ida_loader_info,got_ida_loader_info = Future.create () in
  let ida_brancher_info,got_ida_brancher_info = Future.create () in

  let futures =
    {symbols = (ida_symbols_info, got_ida_symbols_info);
     img = (ida_loader_info, got_ida_loader_info);
     brancher = (ida_brancher_info,got_ida_brancher_info)} in

  let loader = loader got_path futures in
  Project.Input.register_loader name loader;

  register_source futures (module Rooter);
  register_source futures (module Symbolizer);
  register_source futures (module Reconstructor);
  register_brancher_source futures;

  Project.register_pass ~autorun:true ~name:"komapper" (fun proj ->
      (* A module to cache filename *)
      let module Filename = Data.Make(
        struct type t = string
          let version = "0.1"
        end) in

      let file = match Future.peek path with
        (* the first time, save it to digest for this proj *)
        | Some file ->
          let id = Data.Cache.digest ~namespace:"komapper"
              "%s" (Digest.string name) in
          Filename.Cache.save id file;
          Some file
        (* If it fails, the loader info is probably cached. Try get
           it from the cache *)
        | None ->
          let id = Data.Cache.digest ~namespace:"komapper"
              "%s" (Digest.string name) in
          Filename.Cache.load id in
      match file with
      | Some file when (String.is_suffix file ".ko"
                        || String.is_suffix file ".sys") ->
        let id = Data.Cache.digest ~namespace:"ida-brancher"
            "%s" (Digest.file file) in
        let lookup = match Brancher_info.Cache.load id with
          | Some lookup -> lookup
          | None ->
            info "No caching enabled, using futures!";
            read_future (fst futures.brancher) in
        (*printf "%a@." Brancher_info.pp lookup;*)
        let relocs = get_relocs lookup in
        let relocs_other = get_relocs_other lookup in
        if String.is_suffix file ".ko"
        then Ida_komapper.main proj relocs relocs_other
        else Ida_sysmapper.main proj relocs relocs_other
      | Some file -> info "Komapper skipped: no .ko extension"; proj
      | None -> warning "Komapper skipped: no filename from loader or cache.";
        proj)

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
