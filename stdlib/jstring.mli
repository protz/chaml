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

(** Various string utilities. *)

(** Make all your pretty-printers work with buffers and use this to get a
    [Printf.sprintf] *)
val bsprintf: ('a, Buffer.t, unit, string) format4 -> 'a

(** Make all your pretty-printers work with buffers, use them with [%a] and use
    this to get a [Printf.fprintf] *)
val bfprintf : out_channel -> ('a, Buffer.t, unit, unit) format4 -> 'a

(** In case you need to ignore some stuff. *)
val biprintf : ('a, Buffer.t, unit) format -> 'a

(** An imperative buffer of strings. Use [Buf.flush] when you're done. *)
module Buf: sig
  type t
  val create : unit -> t
  val add : t -> string -> unit
  val add_list : t -> string list -> unit
  val flush : t -> string
end
