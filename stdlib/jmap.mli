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

(** Various missing functions from the [Map] module. *)

module Make: functor (M : Map.S) -> sig
  (** Get a list of all keys in a map. *)
  val keys : 'a M.t -> M.key list

  (** [union m1 m2] keeps the values from [m1] *)
  val union : 'a M.t -> 'a M.t -> 'a M.t

  (** [inter m1 m2] keeps the values from [m1] *)
  val inter : 'a M.t -> 'a M.t -> 'a M.t

  (** [minus m1 m2] returns [m1] minus all the elements that are also in [m2],
      that is, m1 \ (m1 ∩ m2) *)
  val minus : 'a M.t -> 'a M.t -> 'a M.t

  (** [xor m1 m2] is ([m1] ∪ [m2]) \ ([m1] ∩ [m2]) *)
  val xor : 'a M.t -> 'a M.t -> 'a M.t

  (** [to_list] translates the map to a list. *)
  val to_list : 'a M.t -> (M.key * 'a) list
end
