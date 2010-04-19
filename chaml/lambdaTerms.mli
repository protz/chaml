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

(** An AST annotated with {!Algebra.SOLVER} types. *)

(** The constraint generator generates a constraint as well as a {!Make.term}
    that represents a well-typed AST when the solving has been done. *)

module Make: functor (S: Algebra.SOLVER) -> sig

  open Algebra.Identifiers

  type term = [
    | `Let of (pattern * term) list * term 
    | `Instance of S.instance * ident
    | `App of term * term
    | `Lambda of pattern * term
    | `Const of
        [ `Char of char | `Int of int | `Float of float | `String of string ]
  ]
  and pattern = [
    | `Var of S.scheme * ident
    | `Tuple of pattern list
  ]
end
