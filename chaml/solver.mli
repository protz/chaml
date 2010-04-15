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

(** The solver works on top of the unifier and the constraint generator. *)

(** This can be forwarded to other modules that depend on a solver. This is
    actually borrowed from [Unify]. *)
module BaseSolver: Algebra.SOLVER

(** Describes a unification or solving error.  *)
type error

(** Create a human-readable representation of an error. *)
val string_of_error: error -> string

(** This is the only useful function. It takes a set of constraints and returns
    a typed AST. It explains that it takes a type constraint that's been built
    with this very solver's data structures. *)
val solve: caml_types:bool -> print_types:bool ->
  Constraint.Make(BaseSolver).type_constraint * LambdaTerms.Make(BaseSolver).term ->
  [`Ok | `Error of error]
