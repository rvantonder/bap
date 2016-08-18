open Core_kernel.Std
open Regular.Std
open Bap.Std

type perm = [`code | `data] [@@deriving sexp]
type section = string * perm * int * (int64 * int)
  [@@deriving sexp]

type image = string * addr_size * section list [@@deriving sexp]

module Img = struct
  type t = image

  include Data.Make(struct
      type t = image
      let version = "0.1"
    end)
end

module Symbols = struct
  type t = (string * int64 * int64) list

  include Data.Make(struct
      type t = (string * int64 * int64) list
      let version = "0.1"
    end)
end

module Brancher_info = struct
  type t = (int64 * int64 option * int64 list) list

  include Data.Make(struct
      type t = (int64 * int64 option * int64 list) list
      let version = "0.1"
    end)
end
