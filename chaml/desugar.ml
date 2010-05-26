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

type cenv = {
  forall: int;
  type_term: DeBruijn.type_term;
  pattern: Core.pattern;
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
       * that allows us to get a pointer to all generated atoms and patterns. *)
      let new_patterns, new_atoms =
        List.split
          (List.map (fun (pat, _, _) -> desugar_pat env pat) pat_coerc_exprs)
      in
      (* We generate e2 with all identifiers in scope *)
      let new_env = introduce (List.flatten new_atoms) env in
      let e2 = desugar_expr new_env e2 in
      (* And then we desugar all of the initial branches in the same previous
       * scope *)
      let gen_branch e2 (_, { young_vars; f_type_term = type_term }, e1) pat = 
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
        (* Generate the coercion *)
        let coercion =
          generate_coerc new_env { pattern = pat; forall = young_vars; type_term }
        in
        let pat = `Coerce (pat, coercion) in
        (* The pattern has already been translated in a first pass. Now check if
         * it's just an identifier (we can use a regular let-binding) or a
         * pattern (then, we use a match) *)
        match pat with
        | `Var atom ->
            assert (coercion = `Id);
            `Let (`Var atom, e1, e2)
        | pat ->
            `Match (e1, [(pat, e2)])
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
              | (`Var _ as v), ([_] as atoms) ->
                  let new_env = introduce atoms env in
                  `Fun (v, arg_type, desugar_expr new_env expr)
              | _ ->
                  assert false
              end

          (* This is the general case. We either have many branches, or a
           * pattern instead of a single var. *)
          | _ ->
            (* First create a fake ident. We don't care about unique names anymore,
             * because atoms have a uniquely generated identifier. *)
            let atom = Atom.fresh (ident "__internal" Location.none) in
            (* Now function is forbidden, only fun x -> with x being a single
             * var. This is where the type of the whole argument turns out to be
             * useful, and this is why we've been forwarding it through the many
             * passes since the beginning. *)
            let var = `Var atom in
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
            `Fun (var, arg_type, mmatch)
      end

  | `Match (_expr, _clblock, _forall, _pat_exprs) ->
      failwith "Match not implemented"

  | `Tuple exprs ->
      let exprs = List.map (desugar_expr env) exprs in
      `Tuple exprs

  | `Const c ->
      let c = desugar_const c in
      `Const c

and desugar_pat env pat =
  match pat with
  | `Var (ident, _typ) ->
      let atom = Atom.fresh ident in
      `Var atom, [atom]

  | `Tuple patterns ->
      let patterns, atoms = List.split (List.map (desugar_pat env) patterns) in
      `Tuple patterns, List.flatten atoms

  | `Or (p1, p2) ->
      let p1, a1 = desugar_pat env p1 in
      let p2, a2 = desugar_pat env p2 in
      `Or (p1, p2), a1 @ a2

  | `Any ->
      `Any, []

(* [generate_coercion] walks down the pattern scheme and the pattern in
 * parallel, and returns a list of coercions needed to properly type this
 * pattern *)
and generate_coerc env { forall; type_term; pattern; } =
  let type_cons_tuple i =
    let fake_list = Jlist.make i () in
    let `Cons (cons_name, _) = Algebra.TypeCons.type_cons_tuple fake_list in
    cons_name
  in
  let concat f l =
    List.fold_left f (List.hd l) (List.tl l)
  in
  match pattern, type_term with
  | `Tuple patterns, `Cons (cons_name, cons_args)
    when cons_name = type_cons_tuple (List.length patterns) ->
      (* Let's move all the variables inside the branches *)
      let gen i pattern type_term =
        let c =
          generate_coerc env { forall; pattern; type_term; }
        in
        `CovarTuple (i, c)
      in
      (* We have the first coercion *)
      let c =
        concat (fun x y -> `Compose (x, y)) (Jlist.map2i gen patterns cons_args)
      in
      (* Explain that we inject all the variables inside the branches *)
      let rec fold forall =
        if forall = 0 then
            `Id
        else
          let c = fold (forall - 1) in
          let c1 = `ForallIntroC (
            `Compose (`ForallElim (`Var DeBruijn.zero), c))
          in
          `Compose (c1, `DistribTuple)
      in
      `Compose (fold forall, c)

  | `Var _, _ ->
      (* Are we still under \Lambdas? If not, then we've got a proper
       * coercion. If we still have some \Lambdas, we must remove those that
       * are useless. *)
      if forall = 0 then
        `Id
      else
        (* Mark all the variables quantified in this scheme
           XXX this probably has a bad complexity *)
        let seen = Array.make forall false in
        let rec walk type_term =
          match type_term with
            | `Var v ->
                let i = DeBruijn.index v in
                if i < forall then
                  seen.(DeBruijn.index v) <- true
            | `Cons (_cons_name, cons_args) ->
                List.iter walk cons_args
        in
        walk type_term;
        (* We remove quantifiers we don't use *)
        let rec fold i =
          if i = 0 then
            `Id
          else
             if not seen.(i-1) then
               `Compose (`ForallElim Algebra.TypeCons.type_cons_bottom, fold (i - 1))
             else
               let c = fold (i - 1) in
               if c = `Id then
                 `Id
               else
                 `ForallIntroC (`Compose (`ForallElim (`Var DeBruijn.zero), c))
        in
        fold forall
                
  | _ ->
      failwith "Only supporting coercions for tuples at the moment\n"

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
