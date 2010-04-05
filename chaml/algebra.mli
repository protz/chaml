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

(** This module defines the essential types that will be used throughout ChaML.
    All those types are parameterized by a ['var] type, which allows us to
    instanciate them with either type variables (as generated by the constraint
    generator) or with unification variables (as used by the unifier and the
    solver).
   
    The types for the type constructors are intentionally left open. This allows
    those functions to be used either with ['var generic_term] or ['var
    inspected_var] which has type aliases desambiguated and is suitable for
    printing. This is used by the type parser in [tests/]. *)

(** An identifier, as encountered in the OCaml parse tree. *)
type ident = [ `Var of Longident.t ] * Location.t

(** This module will be useful many times from now on. It allows one to map
    identifiers to type variables, unification variables, etc. *)
module IdentMap: Map.S with type key = ident

(** This describes a type constructor. The trick is to use one instance per
    constructor so that we can use referential equality == to quickly test
    whether two types are equal. *)
type type_cons = {
  cons_name: string;
  cons_arity: int;
}

(** This is what is called X in ATTAPL *)
type 'var_type generic_var = [
  `Var of 'var_type
]

(** This is what is called T ::= X | F (X1, ..., Xn) in ATTAPL *)
type 'var_type generic_term = [
    'var_type generic_var
  | `Cons of type_cons * 'var_type generic_term list
]

(** Here we differ slightly from the definition in ATTAPL. A scheme is made of a
    list of universally quantified variables, a constraint that has to be
    satisfied, and a mapping from identifiers to variables.
   
    If there is a pattern on the left-hand side of a let binding, then
    generate_constraint_pattern will have to bind several identifiers to type
    variables. This is why we use a IdentMap. (Think of [let x, y = ...] for
    instance.)
  *)
type 'var_type generic_scheme =
    'var_type generic_var list
  * 'var_type generic_constraint
  * 'var_type generic_var IdentMap.t

(** The definition of a constraint. [`Dump] is not really useful, we could use
    [`True], but left for the sake of compatibility with mini.
   
    We might have more than one type scheme if we use [let p1 = e1 and p2 = e2
    ...]  which is why we use a [type_scheme list] in the [`Let] branch.

    We have intentionnaly used [type_var] and not [type_term] in some parts.
    This enforces some invariants.
  *)
and 'var_type generic_constraint = [
    `True
  | `Conj of 'var_type generic_constraint * 'var_type generic_constraint
  | `Exists of 'var_type generic_var list * 'var_type generic_constraint
  | `Equals of 'var_type generic_var * 'var_type generic_term
  | `Instance of ident * 'var_type generic_var
  | `Let of 'var_type generic_scheme list * 'var_type generic_constraint
  | `Dump
]

(** [type_cons cons_name cons_args] allows you to instanciate a type constructor
    with its arguments. This function checks that the type constructor already
    exists and that the arity is correct, so check [algebra.ml] for pre-defined
    ground types. The only exception is the "*" constructor that can be used
    with any number of arguments. The different versions will be created as
    needed. *)
val type_cons : string -> 'a list -> [> `Cons of type_cons * 'a list ]

(** A convenient wrapper to quickly access the arrow constructor. *)
val type_cons_arrow : 'a -> 'a -> [> `Cons of type_cons * 'a list ]

(** A convenient wrapper to quickly access the int constructor. *)
val type_cons_int : [> `Cons of type_cons * 'a list ]

(** A convenient wrapper to quickly access the char constructor. *)
val type_cons_char : [> `Cons of type_cons * 'a list ]

(** A convenient wrapper to quickly access the string constructor. *)
val type_cons_string : [> `Cons of type_cons * 'a list ]

(** A convenient wrapper to quickly access the float constructor. *)
val type_cons_float : [> `Cons of type_cons * 'a list ]

(** A convenient wrapper to quickly access the unit constructor. *)
val type_cons_unit : [> `Cons of type_cons * 'a list ]
