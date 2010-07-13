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

(** The final {!Desugar} translation step sends the {!CamlX.f_expression} into
    this System F-like core language. This is the language we type-check. *)

open DeBruijn

(** A named constructor. Can be Nil, or Cons, or maybe later a full path with a
    module. *)
type label = string

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
  | `ForallCovar of coercion
      (** Apply a coercion under a ∀ *)
  | `ForallElim of type_term
      (** Remove ∀ *)
  | `CovarTuple of int * coercion
      (** If τ1 is a subtype of τ2, then ... * τ1 * ... is a subtype of ... * τ2 * ... *)
  | `DistribTuple
      (** Distribute ∀ under, say, τ1 * τ2 *)
  | `Fold of Atom.t * type_term list
      (** Turn an anonymous sum (say, A + B) into the corresponding named
          isorecursive type, say int t = A + B *)
  | `Unfold of Atom.t * type_term list
      (** The opposite of the coercion above *)
]

type const = [
  | `Char of char
  | `Int of int
  | `Float of float
  | `String of string
]

type pattern = [
    var
  | `Tuple of pattern list
  | `Or of pattern * pattern
  | `Any
  | `Const of const
  | `Coerce of pattern * coercion
  | `Construct of label * pattern list
]

module AtomMap: module type of Jmap.Make(Atom)

type expression = [
  | `TyAbs of expression
  | `TyApp of expression * type_term
  | `Coerce of expression * coercion

  | `Fun of var * type_term * expression
  | `Match of expression * (pattern * expression) list
  | `Let of var * expression * expression 
  | `LetRec of (var * type_term * expression) list * expression
  | `App of expression * expression list

  | `Tuple of expression list
  | `Instance of var
  | `Const of const

  | `Sequence of expression * expression
  | `Construct of label * expression list

  | `Magic of type_term
]

type structure = [
  | `Let of pattern * expression
  | `LetRec of (var * type_term * expression) list
  | `Type of int * Atom.t * type_term
      (* (type arity, type name, anonymous sum or product) *)
] list
