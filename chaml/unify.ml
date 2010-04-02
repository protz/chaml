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
open TypePrinter

(* - An equivalence class of variables is a [unifier_var].
 * - A multi-equation is a set of variables that are all equal to a given [term].
 *
 * - A descriptor represents a class of variables. If they have been equated
 * with a term, then [term] is non-null. Otherwise, it's [None].
 *
 * *)

type descriptor = {
  mutable term: unifier_term option;
  name: string;
  mutable rank: int;
}

and unifier_var = descriptor UnionFind.point
and unifier_term = [
  `Cons of type_cons * unifier_var list
]
and unifier_scheme = unifier_var list * unifier_var

(* A pool contains all the variables with a given rank. *)
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
* - We can use a Hashtbl because all type variables are distinct (although
 * strictly speaking we should use a map for scopes).
* - The map is required because we need different ident maps for each branch of
* multiple simultaneous let bindings. *)
type unifier_env = {
  current_pool: Pool.t;
  uvar_of_tterm: (type_term, unifier_var) Hashtbl.t;
  scheme_of_ident: unifier_scheme IdentMap.t;
}

(* This occurs quite frequently *)
let current_pool env = env.current_pool
let current_rank env = env.current_pool.Pool.rank

(* This creates a new environment with a fresh pool inside that has
 * current_rank+1 *)
let step_env env =
  let new_rank = current_rank env + 1 in
  let new_pool = { Pool.base_pool with Pool.rank = new_rank } in
  { env with current_pool = new_pool }

(* This is mainly for debugging *)
let rec uvar_name: unifier_var -> string =
  let inspect_var: unifier_var -> (descriptor, unifier_var) inspected_var =
    fun uvar ->
    let repr = UnionFind.find uvar in
    match repr.term with
      | Some (`Cons (type_cons, cons_args)) ->
          `Cons (type_cons, cons_args)
      | None ->
          `Key repr
  in
  fun uvar -> match UnionFind.find uvar with
    | { name = s; term = None; _ } ->
        s
    | { name = s; term = Some cons; _ } ->
        let string_of_key: descriptor -> string = fun { name; _ } -> name in
        Printf.sprintf "(%s = %s)" s (string_of_type ~string_of_key uvar inspect_var)

(* Create a fresh variable and add it to the current pool *)
let fresh_unifier_var ?term ?prefix ?name unifier_env =
  let current_pool = current_pool unifier_env in
  let rank = current_rank unifier_env in
  let name =
    match name with
      | None ->
          let prefix = Option.map_none "uvar" prefix in
          fresh_var ~prefix ()
      | Some name ->
          name
  in
  let uvar = UnionFind.fresh { term; name; rank; } in
  Pool.add current_pool uvar;
  uvar

(* Create a fresh copy of a scheme for instanciation *)
let fresh_copy unifier_env (young_vars, scheme_uvar) =
  let mapping = Hashtbl.create 16 in
  let base_rank = (UnionFind.find scheme_uvar).rank in
  let rec fresh_copy uvar =
    let repr = UnionFind.find uvar in
    match repr.term with
      | None ->
          (* We don't create fresh variables. The young variables have already
           * been created for us, so if we can't find it, it's and old variable
           * that we musn't duplicate. *)
          let uvar = match Jhashtbl.find_opt mapping repr with
            | Some uvar -> uvar
            | None -> uvar
          in
          uvar
      | Some (`Cons (cons_name, cons_args)) ->
          let uvar, deep = match Jhashtbl.find_opt mapping repr with
            | Some uvar ->
                if repr.rank < base_rank then
                  uvar, false
                else
                  uvar, true
            | None -> 
                (* Add the variable first to avoid infinite loops. This should
                 * allow some sharing of variables (XXX check this actually
                 * helps). *)
                (* XXX explain *)
                if repr.rank < base_rank then
                  uvar, false
                else
                  let uvar = fresh_unifier_var unifier_env in
                  Hashtbl.add mapping repr uvar;
                  uvar, true
          in
          if deep then
            (* Generate recursively *)
            let cons_args' = List.map fresh_copy cons_args in
            let term = `Cons (cons_name, cons_args') in
            (UnionFind.find uvar).term <- Some term;
            uvar
          else
            uvar
  in
  List.iter
    (fun v ->
       let v' = fresh_unifier_var ~prefix:"dup" unifier_env in
         Error.debug "[Copy] %s is a copy of %s\n" (UnionFind.find v').name
           (UnionFind.find v).name;
         Hashtbl.add mapping (UnionFind.find v) v')
    young_vars;
  let pairs = Jhashtbl.map_list mapping (fun k v -> let n = k.name in
                                   Printf.sprintf "%s: %s" n (uvar_name v))
  in
  Error.debug "[UCopy] Mapping: %s\n" (String.concat ", " pairs);
  fresh_copy scheme_uvar

(* Recursively change terms that depend on constraint vars into unification
 * vars. This function implements the "explicit sharing" concept by making sure
 * we only have pointers to equivalence classes (and not whole terms). This is
 * discussed on p.442, see rule S-NAME-1. This includes creating variables
 * on-the-fly when dealing with type constructors, so that when duplicating the
 * associated var, the pointer to the equivalence class is retained. *)
let rec uvar_of_tterm: unifier_env -> type_term -> unifier_var =
  fun unifier_env type_term ->
    let rec uvar_of_tterm: type_term -> unifier_var = fun tterm ->
    match Jhashtbl.find_opt unifier_env.uvar_of_tterm tterm with
      | Some uvar ->
          uvar
      | None ->
          let term, name = match tterm with
            | `Var s ->
                None, Some s
            | `Cons (cons, args) ->
                let term: unifier_term = `Cons (cons, List.map uvar_of_tterm args) in
                Some term, None
          in
          let uvar = fresh_unifier_var ?name ?term unifier_env in
          Hashtbl.add unifier_env.uvar_of_tterm tterm uvar;
          uvar
    in
    uvar_of_tterm type_term

let debug_unify =
  fun v1 v2 ->
    Error.debug "[UUnify] Unifying %s with %s\n" (uvar_name v1) (uvar_name v2)

(* Update all the mutable data structures to take into account the new equation.
* The descriptor that is kept by UnionFind is that of the *second* argument. *)
let rec unify: unifier_env -> unifier_var -> unifier_var -> unit =
  fun unifier_env v1 v2 ->
  if not (UnionFind.equivalent v1 v2) then
    (* Keeps the second argument's descriptor and updates the rank *)
    let merge v1 v2 =
      let repr1, repr2 = UnionFind.find v1, UnionFind.find v2 in
      let r = min repr1.rank repr2.rank in
      UnionFind.union v1 v2;
      repr2.rank <- r
    in
    match UnionFind.find v1, UnionFind.find v2 with
      | { term = Some t1; _ }, { term = Some t2; _ } ->
          let `Cons (c1, args1) = t1 and `Cons (c2, args2) = t2 in
          if not (c1 == c2) then
            Error.fatal_error "%s cannot be unified with %s\n" c1.cons_name c2.cons_name;
          if not (List.length args1 == List.length args2) then
            Error.fatal_error "wrong number of arguments for this tuple\n";
          List.iter2 (fun arg1 arg2 -> unify unifier_env arg1 arg2) args1 args2;
          merge v1 v2;
      | { term = Some _; _ }, { term = None; _ } ->
          debug_unify v2 v1;
          merge v2 v1;
      | { term = None; _ }, { term = Some _; _ } ->
          debug_unify v2 v1;
          merge v1 v2;
      | { term = None; _ }, { term = None; _ } ->
          debug_unify v2 v1;
          merge v1 v2

(* For printing type schemes *)
let string_of_scheme ident scheme =
  let _, uvar = scheme in
  let inspect_var: unifier_var -> (descriptor, unifier_var) inspected_var =
    fun uvar ->
    let repr = UnionFind.find uvar in
    match repr.term with
      | Some (`Cons (type_cons, cons_args)) ->
          `Cons (type_cons, cons_args)
      | None ->
          `Key repr
  in
  Printf.sprintf "val %s: %s" ident (string_of_type uvar inspect_var)
