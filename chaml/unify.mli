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

(** This module features all the required data structure for unification and
    solving. More specifically, it also provides the {!BaseSolver} module that
    is needed for all other modules to function properly. *)

open Algebra.TypeCons
open Algebra.Identifiers
open Algebra.Core

(** {3 Error handling} *)

(** In case two terms cannot be unified, an error will be returned. *)
type error

(** This forces the client code to deal with it, plus, it can be explained with
    this function. *)
val string_of_error: error -> string

(** {3 Core types} *)

(** This is the descriptor used by [UnionFind]. This is what you get when you do
    [UnionFind.find uvar] where [uvar] is a [unifier_var]. *)
type descriptor = {
  name: string; (** For debugging *)
  id: int; (** This is a globally unique identifier *)
  mutable term: unifier_term option;
  mutable rank: int;
  mutable mark: Mark.t;
}

(** The type of unificator variables. They are often called [uvar] in the code.
    *)
and unifier_var

(** An equivalence class in the unifier is just a multi-equations between an
    arbitrary number of variables and a term. The natural way to represent this
    is to say that all variables share a common descriptor. That descriptor
    might be associated to a term. If it's not, it's only an equation between
    variables.

    When a term is equated with another one, they are unified on-the-fly in
    {!unify}. *)
and unifier_term = [ `Cons of head_symbol * unifier_var list ]

(** A scheme is a list of young variables and a constraint. *)
and unifier_scheme = {
  mutable scheme_var: unifier_var;
}

(** Useful to know what's in the constraint-generated term. *)
type unifier_instance = unifier_var list ref

(** To describe the scheme of a full pattern. This is used later on by the
 * translator to build coercions. *)
type unifier_pscheme = {
  mutable p_uvar: unifier_var;
  mutable p_young_vars: unifier_var list;
}

(** This is for your convenience when dealing with hash tables of unifier vars *)
module Uhashtbl: Jhashtbl.S with type key = descriptor

(** The unifier actually provides the base solver with the necessary stubs to
    create pre-allocated constraints and terms. We need to expose all the
    internals of this module because the solver needs to be aware of the type
    equalities between scheme and unifier_scheme for instance (unless we provide
    wrappers around that which we don't really want to do). The other solution
    is for {!Unify} to provide a unifier_scheme_of_basesolver_scheme funtion. *)
module BaseSolver: sig
  type var = unifier_var
  type scheme = unifier_scheme
  type instance = unifier_instance
  type pscheme = unifier_pscheme

  val new_var: string -> var
  val new_scheme_for_var: var -> scheme
  val new_pscheme_for_var: var -> pscheme
  val new_instance: unit -> instance

  val string_of_var: var -> string
end

(** {3 Utils} *)

(** Obtain the descriptor for a given {unifier_var} *)
val find: unifier_var -> descriptor

(** This a globally unique, thread-safe id *)
val id: unifier_var -> int

(** Get the rank *)
val rank: unifier_var -> int


(** {3 Pools and environments} *)

(** When diving into the left branch of a let construct, all variables that are
    created in the process end up in a {!Pool.t}. We then examine the [Pool]'s
    contents to determine which variables are to be generalized (the young
    variables) and which have been unified with previous unification variables
    (they have a smaller rank). {!unify} takes care of updating the rank with
    the smallest value when unifying two variables. *)
module Pool: sig
  type t = { rank: int; mutable members: unifier_var list; }
  val add: t -> unifier_var -> unit
  val base_pool: t
  val next: t -> t
end

(** This is used by the solver to pass down information through the recursive
    calls. We use a [Hashtbl] to translate {!Algebra.Core.type_var}s into
    {!unifier_var}s because the type variables have globally unique names.
    However, we use a [Map] to translate identifiers into schemes because
    identifiers do have a scope. *)
type unifier_env

(** If you need a specific pool.... *)
val get_pool: unifier_env -> int -> Pool.t

(** If you need a sub-pool, call this function. The one above asserts that the
    pool is in the current authorized range. This one does not. *)
val sub_pool: unifier_env -> Pool.t

(** This is just a wrapper to get the current pool. *)
val current_pool: unifier_env -> Pool.t

(** This is just a wrapper to get the current rank. *)
val current_rank: unifier_env -> int

(** Create a new pool, increment the rank. *)
val step_env: unifier_env -> unifier_env

(** Get the current mapping of schemes to identifiers *)
val get_scheme_of_ident: unifier_env -> unifier_scheme IdentMap.t

(** Set it *)
val set_scheme_of_ident: unifier_env -> unifier_scheme IdentMap.t -> unifier_env

(** Get a fresh environment to start working *)
val fresh_env: unit -> unifier_env

(** {3 Printing and debugging} *)

(** Get the internal name of a {!unifier_var}, annotated with all known
    equations. This is for tracing/debugging. Use like this:
    [Jstring.bsprintf "%a" uvar_name uvar] *)
val uvar_name: Buffer.t -> unifier_var -> unit

(** Print a scheme. Use it to get the type of top-level bindings as a string
    "val f: 'a -> ...". *)
val string_of_scheme: ?debug:unit -> ?caml_types:bool ->
      string -> unifier_scheme -> string

(** {3 Core functions} *)

(** When instanciating a type scheme, we must return a copy the variable that
    represents the type scheme, with all the universally quantified variables in
    the scheme replaced by copies of them. This function takes care of
    avoiding all cycles (fingers crossed!) and returns a fresh copy of the
    scheme's unification variable. *)
val fresh_copy: unifier_env -> unifier_scheme -> unifier_scheme * unifier_var list

(** When the constraint generator requests a variable, the {!Algebra.SOLVER} answers
    with what is said to be a "not ready" variable. We cannot use a variable in
    the solver and the unifier if it's not ready. There is a mark on variable to
    tell if they have been made ready or not, so you should always call this
    function before accessing a variable that's been created by the constraint
    generator. *)
val ensure_ready: unifier_env -> unifier_var -> unit

(** This function transforms a type term (let's say, T = [`Cons ("->", uvar1,
    uvar2)]) into a proper unification variable which is equated with term T. It
    also makes sure all variables are ready before returning. *)
val uvar_of_term: unifier_env -> unifier_var type_term -> unifier_var

(** The main function, called by the solver to unify terms. *)
val unify: unifier_env -> unifier_var -> unifier_var -> [ `Ok | `Error of error ]
