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
type expression = (type_instance, type_scheme option, f_type_var) CamlX.expression
type pattern = (type_instance, type_scheme option) CamlX.pattern
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
  Error.debug "[TLiftAdd] Adding %a\n" uvar_name uvar;
  { fvar_of_uvar = new_map }

let union { fvar_of_uvar = map1 } { fvar_of_uvar = map2 } =
  { fvar_of_uvar = StringMap.union map1 map2 }

(* The core functions *)

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
  let rec translate_expr: env -> (unifier_instance, unifier_scheme, unifier_var) CamlX.expression -> expression = 
    fun env uexpr ->
    match uexpr with
      | `Let (pat_expr_list, introduced_vars, e2) ->
          Error.debug "[TLet] %d vars in this scheme\n" (List.length !introduced_vars);
          let new_env = List.fold_left lift_add env !introduced_vars in
          let pat_expr_list =
            List.map
              (fun (upat, uexpr) ->
                (* We don't assign schemes, so we don't need the fresh variables
                 * *)
                let fpat = translate_pat env ~assign_schemes:false upat in
                (* But when we type e1, we need those new type variables *)
                let fexpr = translate_expr new_env uexpr in
                (fpat, fexpr)
              )
              pat_expr_list
          in
          let new_vars =
            List.map
              (fun uvar -> StringMap.find (UnionFind.find uvar).name new_env.fvar_of_uvar)
              !introduced_vars
          in
          let fexpr = translate_expr new_env e2 in
          `Let (pat_expr_list, ref new_vars, fexpr)

      | `Lambda pat_expr_list ->
           let pat_expr_list = List.map
            (fun (upat, uexpr) ->
              let fpat = translate_pat env ~assign_schemes:true upat in
              let fexpr = translate_expr env uexpr in
              fpat, fexpr
            )
            pat_expr_list
          in
          `Lambda pat_expr_list

      | `Instance (ident, instance) ->
          (* let instance =
            List.map
              (fun x -> StringMap.find (UnionFind.find x).name env.fvar_of_uvar)
              !instance
          in
          `Instance (ident, instance) *)
          failwith "Instance not implemented"

      | `App (_e1, _args) ->
          failwith "App not implemented"

      | `Match (_e1, _pat_expr_list) ->
          failwith "Match not implemented"

      | `Tuple (exprs) ->
          `Tuple (List.map (translate_expr env) exprs)

      | `Const _ as r ->
          r

  (* [translate_pat] just generates patterns as needed. It doesn't try to
   * assign schemes to variables if those are on the left-hand side of a pattern. *)
  and translate_pat: env -> assign_schemes:bool -> (unifier_instance, unifier_scheme) CamlX.pattern -> pattern =
    fun env ~assign_schemes upat ->
    match upat with
      | `Any as r ->
          r

      | `Tuple patterns ->
          `Tuple (List.map (translate_pat env ~assign_schemes) patterns)

      | `Or (p1, p2) ->
          `Or (translate_pat env ~assign_schemes p1, translate_pat env ~assign_schemes p2)

      | `Var (ident, { scheme_var = scheme }) ->
          let scheme =
            if assign_schemes then
              Some (type_term_of_uvar env scheme)
            else
              None
          in
          `Var (ident, scheme)
  in
  translate_expr { fvar_of_uvar = StringMap.empty }

let string_of_t =
  fun _ -> failwith "Not implemented"
