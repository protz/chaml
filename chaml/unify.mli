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
  mutable term: unifier_term option;
  name: string; (** This is just used for tracing and debugging the unifier. *)
  mutable rank: int;
}

(** The type of unificator variables. They are often called [uvar] in the code.
    *)
and unifier_var = descriptor UnionFind.point

(** An equivalence class in the unifier is just a multi-equations between an
    arbitrary number of variables and a term. The natural way to represent this
    is to say that all variables share a common descriptor. That descriptor
    might be associated to a term. If it's not, it's only an equation between
    variables.

    When a term is equated with another one, they are unified on-the-fly in
    {!unify}. *)
and unifier_term = [ `Cons of Algebra.TypeCons.type_cons * unifier_var list ]

(** A scheme is a list of young variables and a constraint. *)
and unifier_scheme = unifier_var list * unifier_var

(** The unifier actually provides the base solver with the necessary stubs to
    create pre-allocated constraints and terms. *)
module BaseSolver: Algebra.SOLVER

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
  val add_list: t -> unifier_var list -> unit
  val base_pool: t
  val next: t -> t
end

(** This is used by the solver to pass down information through the recursive
    calls. We use a [Hashtbl] to translate {!Constraint.type_var}s into
    {!unifier_var}s because the type variables have globally unique names.
    However, we use a [Map] to translate identifiers into schemes because
    identifiers do have a scope. *)
type unifier_env = {
  current_pool: Pool.t;
  uvar_of_tterm: (Constraint.Make(BaseSolver).type_term, unifier_var) Hashtbl.t;
  scheme_of_ident: unifier_scheme Algebra.Identifiers.IdentMap.t;
}

(** This is just a wrapper to get the current pool. *)
val current_pool: unifier_env -> Pool.t

(** This is just a wrapper to get the current rank. *)
val current_rank: unifier_env -> int

(** Create a new pool, increment the rank. *)
val step_env: unifier_env -> unifier_env

(** {3 Printing and debugging} *)

(** Get the internal name of a {!unifier_var}, annotated with all known
    equations. This is for tracing/debugging. Use like this:
    [Jstring.bsprintf "%a" uvar_name uvar] *)
val uvar_name: Buffer.t -> unifier_var -> unit

(** Print a unification variable as a type, useful for error messages. *)
val string_of_uvar: ?string_of_key:(unifier_var -> string) -> ?caml_types:bool ->
      ?young_vars:unifier_var list -> unifier_var -> string

(** Print a scheme. Use it to get the type of top-level bindings as a string
    "val f: 'a -> ...". *)
val string_of_scheme: ?string_of_key:(unifier_var -> string) -> ?caml_types:bool ->
      string -> unifier_var list * unifier_var -> string

(** {3 Core functions} *)

(** When instanciating a type scheme, if the rank of the scheme is equal to the
    current rank, we must create a instance. This function takes care of
    avoiding all cycles (fingers crossed!) and returns a fresh copy of a
    unification variable. *)
val fresh_copy:
  unifier_env -> descriptor UnionFind.point list * unifier_var -> unifier_var

(** Recursively change terms that depend on {!Constraint.type_var}s into
    unification vars. This function implements the "explicit sharing" concept by
    making sure we only have pointers to equivalence classes (and not whole
    terms). This is discussed on p.442, see rule S-NAME-1. This implies
    creating variables on-the-fly when dealing with type constructors, so that
    when duplicating the associated var, the pointer to the equivalence class is
    retained. *)
val uvar_of_tterm: unifier_env -> Algebra.Make(BaseSolver).type_term -> unifier_var

(** The main function, called by the solver to unify terms. *)
val unify: unifier_env -> unifier_var -> unifier_var -> [ `Ok | `Error of error ]
