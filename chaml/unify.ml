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
  mutable term: unification_term option;
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

(* Apply "standard" rules *)
let rec unify unification_env unification_constraint =
  unification_constraint

(* Introduce a new equality into the base set of constraints *)
and unify_terms: unification_env -> unification_term -> unification_term -> unification_constraint -> unification_constraint =
  fun unification_env t1 t2 unification_constraint ->
  begin match t1, t2 with
    | `Cons (c1, args1), `Cons (c2, args2) ->
        if not (c1 == c2) then
          Error.fatal_error "%s cannot be unified with %s\n" c1.cons_name c2.cons_name;
        if not (List.length args1 == List.length args2) then
          Error.fatal_error "wrong number of arguments for this tuple\n";
        let konstraint: unification_constraint =
          List.fold_left2
            (fun c arg1 arg2 -> unify_terms unification_env arg1 arg2 c)
            unification_constraint args1 args2
        in
        konstraint
    | `Var v1, `Var v2 ->
      begin match UnionFind.find v1, UnionFind.find v2 with
        (* NB: can I use == here? *)
        | r1, r2 when r1 = r2 ->
            unification_constraint
        | { term = Some t1 }, { term = Some t2 } ->
            let konstraint = unify_terms unification_env t1 t2 unification_constraint in
            UnionFind.union v1 v2;
            konstraint
        | { term = Some _ }, { term = None } ->
            UnionFind.union v2 v1;
            unification_constraint
        | { term = None }, { term = Some _ } ->
            UnionFind.union v1 v2;
            unification_constraint
        | { term = None }, { term = None } ->
            UnionFind.union v1 v2;
            unification_constraint
      end
    | `Var v, (`Cons _ as t1)
    | (`Cons _ as t1), `Var v ->
        begin match UnionFind.find v with
          | { term = Some t2 } ->
              let konstraint = unify_terms unification_env t1 t2 unification_constraint in
              konstraint
          | { term = None } as descriptor ->
              descriptor.term <- Some t1;
              unification_constraint
        end
    | _ ->
      unification_constraint
  end
