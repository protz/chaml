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

(** A bunch of useful functions for lists. *)

(** Same as [List.split] but for triples instead of pairs. *)
val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list

(** Map a function and then discard the result. *)
val ignore_map : ('a -> 'b) -> 'a list -> unit

(** Iterate a function that also takes the index as an argument. *)
val iteri : (int -> 'a -> unit) -> 'a list -> unit

(** Same as [Jlist.iteri] but with two lists. *)
val iter2i : (int -> 'a -> 'b -> unit) -> 'a list -> 'b list -> unit

(** [append_rev_front l1 l2] is tail-rec and returns [(List.rev l1) :: l2]. *)
val append_rev_front : 'a list -> 'a list -> 'a list

(** Remove duplicates from a list. You can provide a hash function as well as a
    custom equality function. The constraint is that two equal elements must
    have the same hash. Use [Hashtbl.hash_func] if needed. *)
val remove_duplicates :
  ?hash_func:('a -> int) ->
  ?equal_func:('a -> 'a -> bool) -> 'a list -> 'a list

(** Find the biggest element in a list *)
val max: int list -> int

(** Turns [Some a; None; ...] into [a; ...] *)
val filter_some: 'a option list -> 'a list
