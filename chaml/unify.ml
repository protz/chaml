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

open Algebra
open Constraint

(* - An equivalence class of variables is a [unification_var].
 * - A multi-equation is a set of variables that are all equal to a given [term].
 *
 * - A descriptor represents a class of variables. If they have been equated
 * with a term, then [term] is non-null. Otherwise, it's [None].
 *
 * *)

type descriptor = {
  term: unification_term option;
  name: string option;
  rank: int;
}

and unification_var = descriptor UnionFind.point
and unification_term = unification_var generic_term

(* A pool contains all the variables of a given rank *)
module Pool = struct

  type t = {
    rank: int;
    members: unification_var list;
  }

end

(* This is used by the solver to pass information down the recursive calls *)
type unification_env = {
  current_rank: int;
  pools: Pool.t list;
  tvar_to_uvar: (type_var, unification_var) Hashtbl.t
}

(* The knowledge gained so far. *)
type unification_constraint = [
  | `True
  | `False
  | `MultiEquation of unification_var
  | `Conj of unification_constraint * unification_constraint
  | `Exists of unification_var list * unification_constraint
]

(* Recursively change terms that depend on constraint vars into terms that
 * depend on unification vars *)
let rec uterm_of_tterm: unification_env -> type_term -> unification_term =
  fun unification_env type_term ->
    let rec uterm_of_tterm: type_term -> unification_term = function
    | `Var s as tvar ->
        begin match Jhashtbl.find_opt unification_env.tvar_to_uvar tvar with
          | None ->
              let uvar = UnionFind.fresh {
                term = None;
                name = Some s;
                rank = unification_env.current_rank
              }
              in
              Hashtbl.add unification_env.tvar_to_uvar tvar uvar;
              `Var uvar
          | Some uvar ->
              `Var uvar
        end
    | `Cons (cons, args) ->
        `Cons (cons, List.map uterm_of_tterm args)
    in
    uterm_of_tterm type_term

(* Useful when introducing new terms *)
let fresh_unification_var ?term ?name unification_env =
  let uvar = UnionFind.fresh { term; name; rank = unification_env.current_rank } in
  `Var uvar

let rec unify unification_env unification_constraint =
  unification_constraint

and unify_terms unification_env (t1: unification_term) (t2: unification_term) unification_constraint =
  (*let v1: unification_term = fresh_unification_var ~term:t1 unification_env in
  let v2: unification_term = fresh_unification_var ~term:t2 unification_env in*)
  unification_constraint
