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

open DeBruijn

(** For terms *)

type var = [
  | `Var of Atom.t
]

type coercion = [
  | `Id
      (** The identity *)
  | `Compose of coercion * coercion
      (** Chain two coercions *)
  | `ForallIntro
      (** Introduce ∀ *)
  | `ForallIntroC of coercion
      (** Introduce ∀ and apply a coercion under it *)
  | `ForallElim of type_term
      (** Remove ∀ *)
  | `CovarTuple of int * coercion
      (** If τ1 is a subtype of τ2, then ... * τ1 * ... is a subtype of ... * τ2 * ... *)
  | `DistribTuple
      (** Distribute ∀ under, say, τ1 * τ2 *)
]

type pattern = [
    var
  | `Tuple of pattern list
  | `Or of pattern * pattern
  | `Any

  | `Coerce of pattern * coercion
]

type const = [
  | `Char of char
  | `Int of int
  | `Float of float
  | `String of string
  | `Unit
]

type expression = [
  | `TyAbs of expression
  | `TyApp of expression * type_term
  (* | `Coerce of expression * coercion *)

  | `Fun of var * type_term * expression
  | `Match of expression * (pattern * expression) list
  | `Let of var * expression * expression 
  | `App of expression * expression list

  | `Tuple of expression list
  | `Instance of Atom.t
  | `Const of const
]
