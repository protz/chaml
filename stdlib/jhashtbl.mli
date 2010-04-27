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

(** This module adds some useful functions that are compatible with [Hashtbl].
    *)

(** Same as [Hashtbl.find] instead that it returns an option type instead of
    raising an exception. *)
val find_opt : ('a, 'b) Hashtbl.t -> 'a -> 'b option

(** map_list [tbl] [f] returns a list of [f key val] for each value [key]
    associated to a value [val] in [tbl]. *)
val map_list : ('a, 'b) Hashtbl.t -> ('a -> 'b -> 'c) -> 'c list

module type S = sig
  include Hashtbl.S

  val find_opt : 'a t -> key -> 'a option
  val map_list : 'a t -> (key -> 'a -> 'b) -> 'b list
end

(** Functional interface. Also includes the regular [Hashtbl] for convenience. *)
module Make (H : Hashtbl.HashedType): S with type key = H.t
