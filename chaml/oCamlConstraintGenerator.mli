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

(** An OCaml front-end for the constraint generator: takes a [Parsetree.t] and
   returns a {!CamlX.Make.expression} as well as a
   {!Constraint.Make.type_constraint} *)

(** This module makes use of the OCaml parser and lexer, walks the OCaml AST and
    produces constraints suitable for solving later on by ChaML. It depends on
    parts of the OCaml source code. One might want to write another custom
    front-end for another language, though. *)

(** This describes an error encountered during constraint generation. *)
type error

(** Creates a human-readable representation of an error *)
val string_of_error: error -> string

module Make: functor (S: Algebra.SOLVER) -> sig

  (** This follows the global convention: modules that are called by the driver
   * are expected to provide pretty-printers. *)
  val string_of_constraint: pretty_printing:bool -> Constraint.Make(S).type_constraint -> string

  (** The driver calls this function. The client of this module is forced to deal
      with the [`Error] case. *)
  val generate_constraint:
    generalize_match:bool ->
    default_bindings:bool -> Parsetree.structure ->
    [ `Ok of Constraint.Make(S).type_constraint * CamlX.Make(S).structure | `Error of error ]

end
