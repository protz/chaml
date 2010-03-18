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

open Parsetree
open Algebra

let tv_tt x = (x: type_var :> type_term)
let constr_conj = function
  | hd :: tl ->
      List.fold_left (fun x y -> `Conj (x, y)) hd tl
  | _ ->
      assert false

(* Parsetree.pattern 
 *
 * We are given a type var that's supposed to match the given pattern. What we
 * return is a type constraint and a map from identifiers to the corresponding
 * type variables. For instance, generate_constraint_pattern X (a*b) returns
 * \exists Y Z. [ X = Y * Z and a < X and b < Y ] and { a => Y; b => Z }
 *
 * We also return the list of all the variables that have been generated and
 * must be bound existentially for this pattern. The let - binding that encloses
 * us will generate the `Exists constraint for us.
 *
 * NB: one might be tempted to think that the map's keys and the list of
 * existentially bound variables are equal. This is not necessarily true, as we
 * might generate intermediate existential variables that are not bound to a
 * specific identifier.
 *
 * *)
let rec generate_constraint_pattern: type_var -> pattern -> (type_constraint * type_var IdentMap.t * type_var list) =
  fun x { ppat_desc; ppat_loc } ->
    match ppat_desc with
      | Ppat_any ->
          `True, IdentMap.empty, []
      | Ppat_var v ->
          let var = ident v in
          let var_map = IdentMap.add var x IdentMap.empty in
          `True, var_map, []
      | Ppat_tuple patterns ->
        (* as in "JIdentMap" *)
        let module JIM = Jmap.Make(IdentMap) in
        (* This represents the sub patterns. If the pattern is (e1, e2, e3),
         * then we generate x1 x2 x3 such that t = x1 * x2 * x3 *)
        let xis = List.map (fun _ -> fresh_type_var ()) patterns in
        let rec combine known_vars known_map current_constraint_list = function
          | (new_pattern :: remaining_patterns, xi :: xis) ->
              (* sub_vars represents the existential variables that have been
               * generated throughout the pattern *)
              let sub_constraint, sub_map, sub_vars = generate_constraint_pattern xi new_pattern in
              if not (IdentMap.is_empty (JIM.inter known_map sub_map)) then
                failwith "Variable is bound several times in the matching";
              let new_map = JIM.union known_map sub_map in
              let new_constraint_list = sub_constraint :: current_constraint_list in
              (* All the variables that have been generated existentially for
               * this pattern *)
              let new_vars = xi :: sub_vars @ known_vars in
              combine new_vars new_map new_constraint_list (remaining_patterns, xis)
          | ([], []) -> 
              let konstraint = constr_conj current_constraint_list in
              List.rev known_vars, known_map, konstraint
          | _ ->
              assert false
        in
        let pattern_vars, pattern_map, pattern_constraint =
          combine [] IdentMap.empty [] (patterns, xis)
        in
        let xis = (xis: type_var list :> type_term list) in
        let konstraint = `Equals (tv_tt x, type_cons "*" xis) in
        let konstraint = `Conj (konstraint, pattern_constraint) in
        konstraint, pattern_map, pattern_vars
      | Ppat_or (pat1, pat2) ->
        let module JIM = Jmap.Make(IdentMap) in
        let c1, map1, vars1 = generate_constraint_pattern x pat1 in
        let c2, map2, vars2 = generate_constraint_pattern x pat2 in
        let xor_map = JIM.xor map1 map2 in
        if not (IdentMap.is_empty xor_map) then begin
          let bad_ident = List.hd (JIM.keys xor_map) in
          failwith (Printf.sprintf "Variable %s must occur on both sides of this | pattern" (ConstraintPrinter.string_of_ident bad_ident))
        end;
        let constraints =
          IdentMap.fold
            (fun k v acc -> `Equals (tv_tt (IdentMap.find k map2), tv_tt v) :: acc)
            map1
            []
        in
        constr_conj (c1 :: c2 :: constraints), map1, vars1 @ vars2
      | _ -> failwith "This pattern is not implemented\n"

(* Parsetree.expression
 * 
 * - TODO figure out what label and the expression option are for in
 * Pexp_function then do things accordingly. label is probably when the argument
 * is labeled. What is the expression option for?
 *
 * *)
and generate_constraint_expression: type_var -> expression -> type_constraint =
  fun t { pexp_desc; pexp_loc } ->
    match pexp_desc with
      | Pexp_ident x ->
          `Instance (`Var x, tv_tt t)
      | Pexp_constant c ->
          let open Asttypes in
          begin match c with
            | Const_int _ -> `Equals (tv_tt t, type_cons_int)
            | Const_char _ -> `Equals (tv_tt t, type_cons_char)
            | Const_string _ -> `Equals (tv_tt t, type_cons_string)
            | Const_float _ -> `Equals (tv_tt t, type_cons_float)
            | _ -> failwith "This type of constant is not supported."
          end
      | Pexp_function (_, _, pat_expr_list) ->
          (* As in the definition. We could generate fresh variables for each
          * branch of the pattern-matching. The conjunction would then force
          * them to be all equal. However, I find it nicer to share x1 and x2. *)
          let x1 = fresh_type_var ~letter:'x' () in
          let x2 = fresh_type_var ~letter:'x' () in
          let generate_branch (pat, expr) =
            (* ~ [[ pat: X1 ]] *)
            let c1, var_map, generated_vars = generate_constraint_pattern x1 pat in
            (* [[ t: X2 ]] *)
            let c2 = generate_constraint_expression x2 expr in
            (* X1 -> X2 = T *)
            let arrow_constr: type_constraint =
              `Equals (type_cons_arrow (tv_tt x1) (tv_tt x2), (tv_tt t))
            in
            let c2' = `Conj (arrow_constr, c2) in
            let let_constr: type_constraint = `Let ([[], c1, var_map], c2') in
            (* This allows to properly scope the variables that are inner to
             * each pattern. x1 and x2 are a level higher since they are shared
             * accross patterns. This wouldn't change much as the variables are
             * fresh anyway, but let's do that properly! *)
            `Exists (generated_vars, let_constr)
          in
          let constraints = List.map generate_branch pat_expr_list in
          `Exists ([x1; x2], constr_conj constraints)
      | Pexp_apply (e1, label_expr_list) ->
          (* ti: xi *)
          let xis, sub_constraints = List.split
            (List.map
              (fun (_, expr) ->
                let xi = fresh_type_var ~letter:'x' () in
                xi, generate_constraint_expression xi expr
              )
              label_expr_list
            )
          in
          (* build the type constructor t1 -> (t2 -> (... -> (tn -> t))) *)
          let arrow_type = List.fold_right
            type_cons_arrow
            (xis: type_var list :> type_term list)
            (tv_tt t)
          in
          (* \exists x1. *)
          let x1 = fresh_type_var ~letter:'x' () in
          (* x1 = t1 -> ... -> tn *)
          let equals_constr: type_constraint = `Equals (tv_tt x1, arrow_type) in
          (* [[ e1: x1 ]] *)
          let arrow_constr = generate_constraint_expression x1 e1 in
          (* combine both: [[ e1: t1 -> t2 -> ... -> tn -> t ]] *)
          let constr: type_constraint = `Conj (arrow_constr, equals_constr) in
          (* the leftmost expression is an arrow and all the arguments have the right type *)
          let konstraint =
            List.fold_left (fun c1 c2 -> `Conj (c1, c2)) constr sub_constraints
          in
          `Exists (x1 :: xis, konstraint)
      | Pexp_let (rec_flag, pat_expr_list, e2) ->
          if rec_flag <> Asttypes.Nonrecursive then
            failwith "Rec flag not supported";
          let c2 = generate_constraint_expression t e2 in
          `Let (List.map generate_constraint_pat_expr pat_expr_list, c2)
      | Pexp_match (e1, pat_expr_list) ->
          let x1 = fresh_type_var ~letter:'x' () in
          let constr_e1 = generate_constraint_expression x1 e1 in
          if Opts.get_opt "generalize-match" then
            (* We generalize here. See the draft version of ATTAPL p.98 for the
             * exact rule. The important part is that we generate a `Let
             * constraint for each branch and we copy the e1 constraint into each
             * branch. *)
            let generate_branch (pat, expr) =
              let c1, var_map, generated_vars = generate_constraint_pattern x1 pat in
              let c2 = generate_constraint_expression t expr in
              let c = `Conj (constr_e1, c1) in
              let let_constr: type_constraint =
                `Let ([x1 :: generated_vars, c, var_map], c2)
              in
              let_constr
            in
            let constraints = List.map generate_branch pat_expr_list in
            `Exists ([x1], constr_conj constraints)
          else
            let generate_branch (pat, expr) =
              let c1, var_map, generated_vars = generate_constraint_pattern x1 pat in
              let c2 = generate_constraint_expression t expr in
              (* This rule doesn't generalize. This allows *not* to duplicate the
              * e1 constraint. That way, we don't explode with rectypes. *)
              let let_constr: type_constraint = `Let ([[], c1, var_map], c2) in
              `Exists (generated_vars, let_constr)
            in
            let constraints = List.map generate_branch pat_expr_list in
            `Exists ([x1], constr_conj (constr_e1 :: constraints))
      | _ ->
          failwith "This expression is not supported\n"

(* Parsetree.structure
 * 
 * structure_items are only for top-level definitions (modules, types, ...).
 * - Pstr_value is for let x = ...
 * - Pstr_eval is for let _ = ...
 *
 * For let x = ..., we use a fresh type variable T. After constraint resolution
 * is finished, the constraint on T will be the type of the top-level binding we
 * were looking for. The outermost var_map contains the bindings that end up in
 * the environment. A single let-binding can bind multiple variables if the
 * left-hand side is a pattern.
 *
 * The fact that pat_expr_list is a list is because of let ... and ... that are
 * defined simultaneously. We allow that through the type_scheme list in `Let
 * type.
 *
 * For top-level definitions, the variables end up free in the environment.
 *
 * *)
and generate_constraint: structure -> type_constraint =
  fun structure ->
    let generate_constraint_structure_item = fun { pstr_desc; pstr_loc } c2 ->
      match pstr_desc with
        | Pstr_value (rec_flag, pat_expr_list) ->
            if rec_flag <> Asttypes.Nonrecursive then
              failwith "rec flag not implemented\n";
            `Let (List.map generate_constraint_pat_expr pat_expr_list, c2)
        | Pstr_eval expr ->
            let t = fresh_type_var ~letter:'t' () in
            let c = generate_constraint_expression t expr in
            let c = `Exists ([t], c) in
            `Let ([[], c, IdentMap.empty], c2)
        | _ -> failwith "structure_item not implemented\n"
    in
    let default_bindings =
      let plus_scheme =
        let plus_var = fresh_type_var ~letter:'z' () in
        let plus_type =
          type_cons_arrow type_cons_int (type_cons_arrow type_cons_int type_cons_int)
        in
        let plus_map = IdentMap.add (ident "+") plus_var IdentMap.empty in
        [plus_var], `Equals (tv_tt plus_var, plus_type), plus_map
      in
      (* Disabled for the moment as this generates a constraint that looks like
       * a comment *)
      (* let mult_scheme =
        let mult_var = fresh_type_var ~letter:'z' () in
        let mult_type =
          type_cons_arrow type_cons_int (type_cons_arrow type_cons_int type_cons_int)
        in
        let mult_map = IdentMap.add (ident "*") mult_var IdentMap.empty in
        [mult_var], `Equals (tv_tt mult_var, mult_type), mult_map
      in *)
      [plus_scheme]
    in
    let topmost_constraint =
      List.fold_right generate_constraint_structure_item structure `Dump
    in
    `Let (default_bindings, topmost_constraint)

(* Useful for let pattern = expression ... *)
and generate_constraint_pat_expr: pattern * expression -> type_var list * type_constraint * type_var IdentMap.t =
  fun (pat, expr) ->
    let x = fresh_type_var ~letter:'x' () in
    let c1, var_map, generated_vars = generate_constraint_pattern x pat in
    let c1' = generate_constraint_expression x expr in
    let konstraint = `Exists (generated_vars, `Conj (c1, c1')) in
    [x], konstraint, var_map
