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
open CamlX

type env = {
  atom_of_ident: Atom.t IdentMap.t;
}

(* Introduce new identifiers in scope, possibly overriding previously defined
 * ones. *)
let introduce: Atom.t list -> env -> env =
  fun atoms { atom_of_ident } ->
    let atom_of_ident = List.fold_left
      (fun map atom ->
        IdentMap.add (Atom.ident atom) atom map)
      atom_of_ident
      atoms
    in
    { atom_of_ident }

let find: ident -> env -> Atom.t =
  fun ident { atom_of_ident } ->
    IdentMap.find ident atom_of_ident

let rec desugar_expr: env -> CamlX.f_expression -> Core.expression =
  fun env expr ->
  match expr with
  | `Let (pat_coerc_exprs, e2) ->
      (* We have the invariant that all identifiers are distinct, we explicitely
       * checked for that in the constraint generator. This is the first pass
       * that allows us to get a grip on all generated atoms and patterns. *)
      let new_patterns, new_atoms =
        List.split
          (List.map (fun (pat, _, _) -> desugar_pat env pat) pat_coerc_exprs)
      in
      (* We generate e2 with all identifiers in scope *)
      let new_env = introduce (List.flatten new_atoms) env in
      let e2 = desugar_expr new_env e2 in
      (* And then we desugar all of the initial branches in the same previous
       * scope *)
      let gen_branch e2 (_, { coercion; young_vars; _ }, e1) pat = 
        let e1 = desugar_expr env e1 in
        (* Beware, now we must generate proper F terms *)
        let rec add_lambda i e =
          if i > 0 then
            add_lambda (i - 1) (`TyAbs e)
          else
            e
        in
        (* So we generate proper Lambdas *)
        let e1 = add_lambda young_vars e1 in
        (* And apply the coercion *)
        let e1 = `Coerce (e1, coercion) in
        (* The pattern has already been translated in a first pass *)
        `Let (pat, e1, e2)
      in
      (* Wrap everyone around e2 *)
      let expr = List.fold_left2 gen_branch e2 pat_coerc_exprs new_patterns in
      expr

  | `Instance (ident, type_terms) ->
      (* Remember, we have the invariant that the instance variables are in the
       * global order, and so are the scheme variables (fingers crossed)! *)
      let app expr type_term =
        `TyApp (expr, type_term)
      in
      let instance = `Instance (find ident env) in
      List.fold_left app instance type_terms

  | `App (expr, exprs) ->
      let exprs = expr :: exprs in
      let exprs = List.map (desugar_expr env) exprs in
      `App (List.hd exprs, List.tl exprs)

  | `Function (arg_type, pat_exprs) ->
      begin match pat_exprs with
          (* We deal with the trivial case fun x -> where x is already an identifier *)
          | [(`Var _ as v, expr)] ->
              begin match desugar_pat env v with
              | (`Var (_, Some var_type) as v), ([_] as atoms) ->
                  (* Possibly expensive, don't forget -noassert *)
                  assert (arg_type = var_type);
                  let new_env = introduce atoms env in
                  `Fun (v, desugar_expr new_env expr)
              | _ ->
                  assert false
              end

          (* This is the case function p1 -> e1 | p2 -> e2 ... *)
          | _ ->
            (* First create a fake ident. We don't care about unique names anymore,
             * because atoms have a uniquely generated identifier. *)
            let atom = Atom.fresh (ident "__internal" Location.none) in
            (* Now function is forbidden, only fun x -> with x being a single var *)
            let var = `Var (atom, Some arg_type) in
            (* Take an instance of the introduced variable. Because we're in ML,
             * there's no universal quantification on the type of x so there's no type
             * variables to instanciate, so no `TyApp. *)
            let instance = `Instance atom in
            (* Translate the expressions and the patterns *)
            let gen (pat, expr) =
              let pat, atoms = desugar_pat env pat in
              let new_env = introduce atoms env in
              let expr = desugar_expr new_env expr in
              (pat, expr)
            in
            (* Finally return fun x -> match x with [...] *)
            let mmatch = `Match (instance, (List.map gen pat_exprs)) in
            `Fun (var, mmatch)
      end

  | `Match (_expr_type, _expr, _pat_exprs) ->
      failwith "Match not implemented"

  | `Tuple exprs ->
      let exprs = List.map (desugar_expr env) exprs in
      `Tuple exprs

  | `Const c ->
      let c = desugar_const c in
      `Const c

and desugar_pat env pat =
  match pat with
  | `Var (ident, typ) ->
      let atom = Atom.fresh ident in
      `Var (atom, typ), [atom]

  | `Tuple patterns ->
      let patterns, atoms = List.split (List.map (desugar_pat env) patterns) in
      `Tuple patterns, List.flatten atoms

  | `Or (p1, p2) ->
      let p1, a1 = desugar_pat env p1 in
      let p2, a2 = desugar_pat env p2 in
      `Or (p1, p2), a1 @ a2

  | `Any ->
      `Any, []

and desugar_const const =
  match const with
  | `Float f ->
      let f = float_of_string f in
      `Float f
  | `Char _ | `Int _ | `String _ | `Unit as x ->
      x

let desugar expr =
  let env = { atom_of_ident = IdentMap.empty } in
  desugar_expr env expr
