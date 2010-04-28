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

open Algebra.Identifiers
open Unify

type f_type_var = { index: int; }
type type_var = f_type_var Algebra.Core.type_var
type type_term = [
    type_var
  | `Cons of Algebra.TypeCons.type_cons * type_term list
  | `Forall of type_term
]

type type_instance = f_type_var list
type type_scheme = type_term
type expression = (type_instance, type_scheme) CamlX.expression
type pattern = (type_instance, type_scheme) CamlX.pattern
type t = expression

module DeBruijn = struct
  let lift: int -> type_term -> type_term =
    fun _ _ -> assert false

  let subst: type_term -> f_type_var -> type_term =
    fun _ _ -> assert false
end

module StringMap = Jmap.Make(String)

(* Various helpers to work with environments *)

type env = {
  fvar_of_uvar: f_type_var StringMap.t;
}

let lift_add env uvar =
  let new_map =
    StringMap.map (fun x -> { index = x.index + 1 }) env.fvar_of_uvar
  in
  let new_map =
    StringMap.add (UnionFind.find uvar).name { index = 1 } new_map
  in
  { fvar_of_uvar = new_map }

let union { fvar_of_uvar = map1 } { fvar_of_uvar = map2 } =
  { fvar_of_uvar = StringMap.union map1 map2 }

(* The core functions *)

(* We don't keep a list of universally quantified variables for each scheme, so
 * it's up to us to walk down the scheme and find all variables with rank -1.
 * *)
let type_vars_of_scheme scheme =
  let young_vars = Uhashtbl.create 16 in
  let seen = Uhashtbl.create 16 in
  let rec walk uvar =
    let repr = UnionFind.find uvar in
    match Uhashtbl.find_opt seen repr with
    | Some _ ->
        ()
    | None ->
        match repr.term with
        | None ->
            if repr.rank = (-1) then
              Uhashtbl.add young_vars repr uvar;
        | Some (`Cons (_cons_name, cons_args)) ->
            Uhashtbl.add seen repr uvar;
            if repr.rank = (-1) then
              List.iter walk cons_args;
  in
  walk scheme;
  Uhashtbl.map_list young_vars (fun _k v -> v)

(* Once all the right variables are in the environment, we simply transcribe a
 * scheme into the right fscheme structure (it's a type_term) *)
let type_term_of_uvar env uvar =
  let rec type_term_of_uvar uvar =
    let repr = UnionFind.find uvar in
    match repr.term with
    | None ->
        let fvar = StringMap.find repr.name env.fvar_of_uvar in
        `Var fvar
    | Some (`Cons (cons_name, cons_args)) ->
        `Cons (cons_name, List.map type_term_of_uvar cons_args)
  in
  type_term_of_uvar uvar 

let translate =
  let rec translate_expr: env -> (unifier_instance, unifier_scheme) CamlX.expression -> expression = 
    fun env uexpr ->
    match uexpr with
      | `Let (pat_expr_list, e2) ->
          let pat_expr_list, new_env =
            List.fold_left
              (fun (acc, future_env) (upat, uexpr) ->
                let new_env, fpat = translate_pat ~introduce_vars:true env upat in
                let fexpr = translate_expr new_env uexpr in
                (fpat, fexpr) :: acc, union new_env future_env
              )
              ([], env)
              pat_expr_list
          in
          let pat_expr_list = List.rev pat_expr_list in
          let fexpr = translate_expr new_env e2 in
          `Let (pat_expr_list, fexpr)

      | `Lambda pat_expr_list ->
          let pat_expr_list = List.map
            (fun (upat, uexpr) ->
              let _same_env, fpat = translate_pat ~introduce_vars:false env upat in
              let fexpr = translate_expr env uexpr in
              fpat, fexpr
            )
            pat_expr_list
          in
          `Lambda pat_expr_list

      | `Instance (ident, instance) ->
          let instance =
            List.map
              (fun x -> StringMap.find (UnionFind.find x).name env.fvar_of_uvar)
              !instance
          in
          `Instance (ident, instance)

      | `App (_e1, _args) ->
          failwith "App not implemented"

      | `Match (_e1, _pat_expr_list) ->
          failwith "Match not implemented"

      | `Tuple (exprs) ->
          `Tuple (List.map (translate_expr env) exprs)

      | `Const _ as r ->
          r

  (* [translate_pat] is the function that introduces new Λ-bindings in the
   * environment. It returns a new environment where all type variables have
   * been shifted as needed and the map updated to point to the right indices. *)
  and translate_pat: env -> introduce_vars:bool -> (unifier_instance, unifier_scheme) CamlX.pattern -> env * pattern =
    fun env ~introduce_vars upat ->
    match upat with
      | `Any as r ->
          env, r

      | `Tuple patterns ->
          assert (not introduce_vars);
          let patterns =
            List.map
              (fun upat ->
                let _same_env, fpat = translate_pat env ~introduce_vars:false upat in
                fpat
              )
              patterns
          in
          env, `Tuple patterns

      | `Or (_p1, _p2) ->
          failwith "Or not implemented"
          (* `Or (translate_pat p1, translate_pat p2) *)

      | `Var (ident, { scheme_var = scheme }) ->
          if introduce_vars then
            let vars = type_vars_of_scheme scheme in
            let new_env = List.fold_left lift_add env vars in
            let new_type = type_term_of_uvar new_env scheme in
            let new_type = List.fold_left (fun acc _x -> `Forall acc) new_type vars in
            new_env, `Var (ident, new_type)
          else
            let new_type = type_term_of_uvar env scheme in
            env, `Var (ident, new_type)
  in
  translate_expr { fvar_of_uvar = StringMap.empty }

let string_of_t =
  fun _ -> failwith "Not implemented"
