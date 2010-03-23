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
and unification_term = [
  `Cons of type_cons * unification_var list
]

(* A pool contains all the variables with a given rank *)
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


(* Recursively change terms that depend on constraint vars into unification
 * vars. This function implements the "explicit sharing" concept by making sure
 * we only have pointers to equivalence classes (and not whole terms). This is
 * discussed on p.442, see rule S-NAME-1. This includes creating variables
 * on-the-fly when dealing with type constructors, so that when duplicating the
 * associated var, the pointer to the equivalence class is retained. *)
let rec uvar_of_tterm: unification_env -> type_term -> unification_var =
  fun unification_env type_term ->
    let rec uvar_of_tterm: type_term -> unification_var = function
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
              uvar
          | Some uvar ->
              uvar
        end
    | `Cons (cons, args) ->
        let uterm = `Cons (cons, List.map uvar_of_tterm args) in
        let uvar = UnionFind.fresh {
          term = Some uterm;
          name = None;
          rank = unification_env.current_rank
        }
        in
        uvar
    in
    uvar_of_tterm type_term

(* Update all the mutable data structures to take into account the new equation *)
let rec unify: unification_env -> unification_var -> unification_var -> unit =
  fun unification_env v1 v2 ->
  begin match UnionFind.find v1, UnionFind.find v2 with
    (* NB: can I use == here? *)
    | r1, r2 when r1 = r2 ->
        ()
    | { term = Some t1 }, { term = Some t2 } ->
        let `Cons (c1, args1) = t1 and `Cons (c2, args2) = t2 in
        if not (c1 == c2) then
          Error.fatal_error "%s cannot be unified with %s\n" c1.cons_name c2.cons_name;
        if not (List.length args1 == List.length args2) then
          Error.fatal_error "wrong number of arguments for this tuple\n";
        List.iter2 (fun arg1 arg2 -> unify unification_env arg1 arg2) args1 args2;
        UnionFind.union v1 v2;
    | { term = Some _ }, { term = None } ->
        UnionFind.union v2 v1;
    | { term = None }, { term = Some _ } ->
        UnionFind.union v1 v2;
    | { term = None }, { term = None } ->
        UnionFind.union v1 v2;
  end
