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

(** This is what a solver is. This allows us to pre-allocate solver structures
    right at the beginning of constraint generation. However, we need some
    abstraction otherwise the dependencies would be really messy. *)
module type SOLVER = sig
  type var
  type scheme
  type instance

  val new_var: string -> var
  val new_scheme: unit -> scheme
  val new_instance: unit -> instance

  (** Names are guaranteed to be unique. So you can consider this as a key for
      each variable. If you need to do hashconsing, do it on the name of the
      variable, not the variable itself. (Variables with different hashes might
      have identical names). *)
  val string_of_var: var -> string
end

(** This module contains everything related to type constructors. This is
    separated from the rest as in {!Unify} we need to define first the types
    that make up the {!SOLVER} and then instanciate an {!Algebra.Make}. *)
module TypeCons: sig

  (** {3 Type constructors and helpers} *)

  (** This describes a type constructor. The trick is to use one instance per
      constructor so that we can use referential equality == to quickly test
      whether two types are equal. *)
  type type_cons = {
    cons_name: string;
    cons_arity: int;
  }

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

end

(** Once again, putting this in a separate module is not necessary strictly
    speaking, but we want to easily have a IdentMap in the scope that is exactly
    the same everywhere. With multiple instanciations, this was getty hairy. Now
    we can do [open Algebra.Identifiers] and this works as well. *)
module Identifiers: sig

  (** {3 Identifiers} *)

  (** An identifier *)
  type long_ident
  type ident = long_ident * Location.t

  (** A wrapper to create an ident *)
  val ident: string -> Location.t -> ident

  (** Print it *)
  val string_of_ident: ident -> string

  (** This module will be useful many times from now on. It allows one to map
      identifiers to type variables, unification variables, etc. *)
  module IdentMap: Map.S with type key = ident

  (** Generate globally unique names. *)
  val fresh_name: ?prefix:string -> unit -> string

end

module Make: functor (S: SOLVER) -> sig

  open S

  (** {3 Error handling} *)

  (** Some operations can throw exceptions (arity mismatch, etc.) At the moment,
      only {!type_cons} can have such a behaviour. *)
  type error

  (** We use exceptions here because [Algebra] is an internal module, so we want
      to walk up the stack in case something goes wrong deep in unification or in
      solving. The modules that are meant to be used by client code do not throw
      exceptions. *)
  exception Error of error

  (** Create a human-readable representation of an error. *)
  val string_of_error: error -> string

  (** {3 Core types} *)

  (** This is what is called X in ATTAPL *)
  type type_var = [
    `Var of var
  ]

  (** This is what is called T ::= X | F (X1, ..., Xn) in ATTAPL. Used in many
      places. *)
  type type_term = [
      type_var
    | `Cons of TypeCons.type_cons * type_term list
  ]

end
