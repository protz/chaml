(*****************************************************************************)
(*  ChaML, a type-checker that uses constraints and a kernel language        *)
(*  Copyright (C) 2010 Jonathan Protzenko                                    *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 3 of the License, or        *)
(*  (at your option) any later version.                                      *)
(*                                                                           *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                           *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                           *)
(*****************************************************************************)

let bsprintf fmt =
  Printf.kbprintf Buffer.contents (Buffer.create 16) fmt

let bfprintf oc fmt =
  Printf.kbprintf (Buffer.output_buffer oc) (Buffer.create 16) fmt

let buf = Buffer.create 0
let biprintf fmt = Printf.ifprintf buf fmt

module Buf: sig
  type t
  val create: unit -> t
  val add: t -> string -> unit
  val add_list: t -> string list -> unit
  val flush: t -> string
end = struct
  type t = string list ref

  let create () =
    ref []

  let add buf s =
    buf := s :: !buf

  let add_list buf l =
    buf := Jlist.append_rev_front l !buf

  let flush buf =
    let l = List.rev !buf in
    buf := [];
    String.concat "" l
end
