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

(** Transform a [ParseTree] from the OCaml frontend into a set of constraints.
    *)

(** These types are all used for constraint generation. *)

(** This is the main type: the type of constraints. *)
type type_constraint = string Algebra.generic_constraint

(** This is the type of type variables used inside constraints. *)
type type_var = string Algebra.generic_var

(** A term is made of either a type variable or a constructor. *)
type type_term = string Algebra.generic_term

(** The type scheme used for [`Let] constraints. *)
type type_scheme = string Algebra.generic_scheme

(** As we use polymorphic variants, this quick wrapper allows you to subtype a
    [type_var] into a [type_term]. *)
val tv_tt : type_var -> type_term

(** A utility function that generates fresh names on demand. Used both inside
    [Constraint] and [Unify]. *)
val fresh_var : ?prefix:string -> unit -> string

(** This is the main function, use it to generate the constraint. *)
val generate_constraint: generalize_match:bool -> default_bindings:bool -> Parsetree.structure -> type_constraint
