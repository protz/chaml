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

(** Some helpers to work with types represented using De Bruijn indices. *)

(** The type of a De Bruijn variable *)
type t

(** These are {!TypePrinter}-compatible types. *)
type type_var = t Algebra.Core.type_var

(** This one has [`Forall] as a bonus. [`Forall] only appears in {!TypeCheck},
    not in {!Desugar}. *)
type type_term = [
    type_var
  | `Cons of Algebra.TypeCons.head_symbol * type_term list
  | `Forall of type_term
  | `Sum of (string * type_term list) list
  | `Prod of (string * type_term list) list
  | `Named of Atom.t * type_term list
]

(** Lift a single variable *)
val lift_t: t -> t

(** Lift a whole term (do +1 on all indices) *)
val lift: type_term -> type_term

(** Get the index of a variable *)
val index: t -> int

(** The 0-th variable *)
val zero: t

(** The i-th variables *)
val of_int: int -> t

(** [subst t2 n t1] substitutes t2 for n in t1. *)
val subst: type_term -> t -> type_term -> type_term

(** These use {!TypePrinter} internally *)
val string_of_t: t -> string

(** This one prints nested $\forall$s *)
val string_of_type_term: type_term -> string
