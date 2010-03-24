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

(* - An equivalence class of variables is a [unifier_var].
 * - A multi-equation is a set of variables that are all equal to a given [term].
 *
 * - A descriptor represents a class of variables. If they have been equated
 * with a term, then [term] is non-null. Otherwise, it's [None].
 *
 * *)

type descriptor = {
  mutable term: unifier_term option;
  name: string option;
  rank: int;
}

and unifier_var = descriptor UnionFind.point
and unifier_term = [
  `Cons of type_cons * unifier_var list
]
and unifier_scheme = unifier_var generic_scheme

(* A pool contains all the variables with a given rank *)
module Pool = struct

  type t = {
    rank: int;
    mutable members: unifier_var list;
  }

  let add t v =
    t.members <- v :: t.members

  let add_list t l =
    t.members <- l @ t.members

  let base_pool = {
    rank = 0;
    members = [];
  }

  let next t = {
    rank = t.rank + 1;
    members = [];
  }

end

(* This is used by the solver to pass information down the recursive calls.
* - We can use a Hashtbl because all variables are distinct (although strictly
* speaking we should use a map for scopes.
* - The map is required because we need different ident maps for each branch of
* multiple simultaneous let bindings. *)
type unifier_env = {
  pools: Pool.t list;
  tvar_to_uvar: (type_var, unifier_var) Hashtbl.t;
  ident_to_uvar: unifier_var IdentMap.t;
}

let step_env env = { env with pools = (Pool.next (List.hd env.pools)) :: env.pools }
let current_pool env = List.hd env.pools


(* Recursively change terms that depend on constraint vars into unification
 * vars. This function implements the "explicit sharing" concept by making sure
 * we only have pointers to equivalence classes (and not whole terms). This is
 * discussed on p.442, see rule S-NAME-1. This includes creating variables
 * on-the-fly when dealing with type constructors, so that when duplicating the
 * associated var, the pointer to the equivalence class is retained. *)
let rec uvar_of_tterm: unifier_env -> type_term -> unifier_var =
  fun unifier_env type_term ->
    let rec uvar_of_tterm: type_term -> unifier_var = function
    | `Var s as tvar ->
        begin match Jhashtbl.find_opt unifier_env.tvar_to_uvar tvar with
          | None ->
              let uvar = UnionFind.fresh {
                term = None;
                name = Some s;
                rank = (current_pool unifier_env).Pool.rank
              }
              in
              Hashtbl.add unifier_env.tvar_to_uvar tvar uvar;
              Pool.add (current_pool unifier_env) uvar;
              uvar
          | Some uvar ->
              uvar
        end
    | `Cons (cons, args) ->
        let uterm = `Cons (cons, List.map uvar_of_tterm args) in
        let uvar = UnionFind.fresh {
          term = Some uterm;
          name = None;
          rank = (current_pool unifier_env).Pool.rank
        }
        in
        Pool.add (current_pool unifier_env) uvar;
        uvar
    in
    uvar_of_tterm type_term

(* Update all the mutable data structures to take into account the new equation *)
let rec unify: unifier_env -> unifier_var -> unifier_var -> unit =
  fun unifier_env v1 v2 ->
  if not (UnionFind.equivalent v1 v2) then
    match UnionFind.find v1, UnionFind.find v2 with
      | { term = Some t1 }, { term = Some t2 } ->
          let `Cons (c1, args1) = t1 and `Cons (c2, args2) = t2 in
          if not (c1 == c2) then
            Error.fatal_error "%s cannot be unified with %s\n" c1.cons_name c2.cons_name;
          if not (List.length args1 == List.length args2) then
            Error.fatal_error "wrong number of arguments for this tuple\n";
          List.iter2 (fun arg1 arg2 -> unify unifier_env arg1 arg2) args1 args2;
          UnionFind.union v1 v2;
      | { term = Some _ }, { term = None } ->
          UnionFind.union v2 v1;
      | { term = None }, { term = Some _ } ->
          UnionFind.union v1 v2;
      | { term = None }, { term = None } ->
          UnionFind.union v1 v2;
