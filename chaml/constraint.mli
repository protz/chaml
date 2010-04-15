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

(** The representation of constraints is defined in this module. *)

(** This module also features, among other things, subtypers {!Make.tv_tt} and
    {!Make.tvl_ttl}, as well as some pretty printers. *)

module Make: functor (S: Algebra.SOLVER) -> sig

  (* To get the ident type in scope. *)
  open Algebra.Identifiers

  (** Here we differ slightly from the definition in ATTAPL. A scheme is made of a
      list of universally quantified variables, a constraint that has to be
      satisfied, and a mapping from identifiers to variables.

      If there is a pattern on the left-hand side of a let binding, then
      generate_constraint_pattern will have to bind several identifiers to type
      variables. This is why we use a IdentMap. (Think of [let x, y = ...] for
      instance.)
    *)
  type type_scheme =
      Algebra.Make(S).type_var list
    * type_constraint
    * (Algebra.Make(S).type_var * S.scheme) IdentMap.t

  (** The definition of a constraint. [`Dump] is not really useful, we could use
      [`True], but left for the sake of compatibility with mini.

      We might have more than one type scheme if we use [let p1 = e1 and p2 = e2
      ...]  which is why we use a [type_scheme list] in the [`Let] branch.

      We have intentionnaly used [generic_var] and not [generic_term] in some
      parts. This enforces some invariants.
    *)
  and type_constraint = [
      `True
    | `Conj of type_constraint * type_constraint
    | `Exists of Algebra.Make(S).type_var list * type_constraint
    | `Equals of Algebra.Make(S).type_var * Algebra.Make(S).type_term
    | `Instance of ident * Algebra.Make(S).type_var
    | `Let of type_scheme list * type_constraint
  ]

  (** We enforce some invariants by requiring that in some places we deal with a
      variable and not a term. However, we often need to subtype. This function
      provides a quick and convenient way to do that. *)
  val tv_tt: Algebra.Make(S).type_var -> Algebra.Make(S).type_term

  (** Same wrapper for convenience. *)
  val tvl_ttl: Algebra.Make(S).type_var list -> Algebra.Make(S).type_term list


  (** A pretty-printer for constraints. Pretty-prints in a format suitable for
      reading by mini. *)
  module PrettyPrinter: sig
    val string_of_type_var: Algebra.Make(S).type_var -> string
    val string_of_constraint: pretty_printing:bool -> type_constraint -> string
  end

end
