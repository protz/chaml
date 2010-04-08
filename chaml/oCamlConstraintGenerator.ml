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
open Error
open Constraint

module IdentMap = Algebra.IdentMap

type error =
  | NotImplemented of string * Location.t
  | VariableBoundSeveralTimes of string * Location.t
  | VariableMustOccurBothSides of string * Location.t
  | AlgebraError of Algebra.error

exception Error of error
let raise_error e = raise (Error e)

let fresh_type_var ?letter () =
  let prefix = Option.map (String.make 1) letter in
  `Var (fresh_name ?prefix ())

let random_ident_name () = Filename.basename (Filename.temp_file "" "")

(* Returns c_1 and (c_2 and ( ... and c_n)) *)
let constr_conj = function
  | hd :: tl ->
      List.fold_left (fun x y -> `Conj (x, y)) hd tl
  | _ ->
      assert false

let generate_constraint =
  fun ~generalize_match:opt_generalize_match
      ~default_bindings:opt_default_bindings
      structure ->

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
            let var = ident v ppat_loc in
            let var_map = IdentMap.add var x IdentMap.empty in
            `True, var_map, []
        | Ppat_tuple patterns ->
          (* as in "JIdentMap" *)
          let module JIM = Jmap.Make(IdentMap) in
          (* This represents the sub patterns. If the pattern is (e1, e2, e3),
           * then we generate x1 x2 x3 such that t = x1 * x2 * x3 *)
          let xis = List.map (fun _ -> fresh_type_var ()) patterns in
          (* This function uses known_* and current_constraint_list as
           * accumulators. It is tail-recursive and combines all the sub-patterns
           * for the members of the tuple into one big pattern. *)
          let rec combine known_vars known_map current_constraint_list = function
            | (new_pattern :: remaining_patterns, xi :: xis) ->
                (* sub_vars represents the existential variables that have been
                 * generated throughout the pattern *)
                let sub_constraint, sub_map, sub_vars = generate_constraint_pattern xi new_pattern in
                let inter_map = JIM.inter known_map sub_map in
                if not (IdentMap.is_empty inter_map) then begin
                  let bad_ident = string_of_ident (List.hd (JIM.keys inter_map)) in
                  raise_error (VariableBoundSeveralTimes (bad_ident, ppat_loc))
                end;
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
          let konstraint = `Equals (x, type_cons "*" (tvl_ttl xis)) in
          let konstraint = `Conj (konstraint, pattern_constraint) in
          konstraint, pattern_map, pattern_vars
        | Ppat_or (pat1, pat2) ->
          (* Ppat_or example: match ... with pat1 | pat2 -> ...
           *
           * It's the opposite of the pattern above: we want every bound identifier
           * to occur on both sides. The folding allows use to generate equality
           * constraints for each of the type variables that's been generated on
           * the two sides. *)
          let module JIM = Jmap.Make(IdentMap) in
          let c1, map1, vars1 = generate_constraint_pattern x pat1 in
          let c2, map2, vars2 = generate_constraint_pattern x pat2 in
          let xor_map = JIM.xor map1 map2 in
          if not (IdentMap.is_empty xor_map) then begin
            let bad_ident = string_of_ident (List.hd (JIM.keys xor_map)) in
            raise_error (VariableMustOccurBothSides (bad_ident, ppat_loc))
          end;
          let constraints =
            IdentMap.fold
              (fun k v acc -> `Equals (IdentMap.find k map2, tv_tt v) :: acc)
              map1
              []
          in
          constr_conj (c1 :: c2 :: constraints), map1, vars1 @ vars2
        | _ ->
            raise_error (NotImplemented ("some pattern", ppat_loc))

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
        | Pexp_ident (Longident.Lident x) ->
            `Instance ((ident x pexp_loc), t)
        | Pexp_constant c ->
            let open Asttypes in
            begin match c with
              | Const_int _ -> `Equals (t, type_cons_int)
              | Const_char _ -> `Equals (t, type_cons_char)
              | Const_string _ -> `Equals (t, type_cons_string)
              | Const_float _ -> `Equals (t, type_cons_float)
              | _ -> raise_error (NotImplemented ("int32 or int64 or intnative", pexp_loc))
            end
        | Pexp_function (_, _, pat_expr_list) ->
            (* As in the definition. We could generate fresh variables for each
             * branch of the pattern-matching. The conjunction would then force
             * them to be all equal. However, I find it nicer to share x1 and x2.
             * *)
            let x1 = fresh_type_var ~letter:'x' () in
            let x2 = fresh_type_var ~letter:'x' () in
            (* X1 -> X2 = T *)
            let arrow_constr: type_constraint =
              `Equals (t, type_cons_arrow (tv_tt x1) (tv_tt x2))
            in
            let generate_branch (pat, expr) =
              (* roughly [[ pat: X1 ]] *)
              let c1, var_map, generated_vars = generate_constraint_pattern x1 pat in
              (* [[ t: X2 ]] *)
              let c2 = generate_constraint_expression x2 expr in
              let let_constr: type_constraint = `Let ([[], c1, var_map], c2) in
              (* This allows to properly scope the variables that are inner to
               * each pattern. x1 and x2 are a level higher since they are shared
               * accross patterns. This wouldn't change much as the variables are
               * fresh anyway, but let's do that properly! *)
              `Exists (generated_vars, let_constr)
            in
            let constraints = List.map generate_branch pat_expr_list in
            `Exists ([x1; x2], constr_conj (arrow_constr :: constraints))
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
            let arrow_type = List.fold_right type_cons_arrow (tvl_ttl xis) (tv_tt t) in
            (* \exists x1. *)
            let x1 = fresh_type_var ~letter:'x' () in
            (* x1 = t1 -> ... -> tn *)
            let equals_constr: type_constraint = `Equals (x1, arrow_type) in
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
            (* Once again, the list of pattern/expressions is here because of
             * let ... and ... in e2 (multiple simultaneous definitions *)
            if rec_flag <> Asttypes.Nonrecursive then
              raise_error (NotImplemented ("rec flag", pexp_loc));
            let c2 = generate_constraint_expression t e2 in
            `Let (List.map generate_constraint_pat_expr pat_expr_list, c2)
        | Pexp_match (e1, pat_expr_list) ->
            if opt_generalize_match then
              (* We generalize here. See the draft version of ATTAPL p.98 for the
               * exact rule. The important part is that we generate a `Let
               * constraint for each branch. Instead of copying the base
               * constraint into each branch, we use a `Let-binding and add an
               * instanciation constraint into each branch. This allows us to
               * simplify the constraint beforehand and perform better. *)
              let print_var_name buf () =
                Buffer.add_string buf (PrettyPrinter.string_of_type_var t)
              in
              Error.debug
                "[CG] Generalizing match constraint on %a\n" print_var_name ();
              (* This is going to be simplified first *)
              let x1 = fresh_type_var ~letter:'x' () in
              let ident1 = ident (random_ident_name ()) Location.none in
              let constr_e1 = generate_constraint_expression x1 e1 in
              (* Each branch has its instance of the type scheme. *)
              let generate_branch (pat, expr) =
                (* Create a fresh variable *)
                let y = fresh_type_var ~letter:'y' () in
                (* It's an instance of the scheme *)
                let instance_constr = `Instance (ident1, y) in
                (* It also satisfies the constraints of the pattern *)
                let c1, var_map, generated_vars =
                  generate_constraint_pattern y pat
                in
                let c = constr_conj [instance_constr; c1] in
                (* Generate constraints for the expression *)
                let c2 = generate_constraint_expression t expr in
                let let_constr: type_constraint =
                  `Let ([y :: generated_vars, c, var_map], c2)
                in
                let_constr
              in
              let constraints = List.map generate_branch pat_expr_list in
              let map = IdentMap.add ident1 x1 IdentMap.empty in
              let scheme = [x1], constr_e1, map in
              `Let ([scheme], constr_conj constraints)
            else
              let x1 = fresh_type_var ~letter:'x' () in
              let constr_e1 = generate_constraint_expression x1 e1 in
              let generate_branch (pat, expr) =
                let c1, var_map, generated_vars = generate_constraint_pattern x1 pat in
                let c2 = generate_constraint_expression t expr in
                (* This rule doesn't generalize, ocaml-style. *)
                let let_constr: type_constraint = `Let ([[], c1, var_map], c2) in
                `Exists (generated_vars, let_constr)
              in
              let constraints = List.map generate_branch pat_expr_list in
              `Exists ([x1], constr_conj (constr_e1 :: constraints))
        | _ ->
            raise_error (NotImplemented ("some expression", pexp_loc))

  (* Parsetree.structure
   *
   * structure_items are only for top-level definitions inside modules
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
                raise_error (NotImplemented ("rec flag", pstr_loc));
              `Let (List.map generate_constraint_pat_expr pat_expr_list, c2)
          | Pstr_eval expr ->
              let t = fresh_type_var ~letter:'t' () in
              let c = generate_constraint_expression t expr in
              let c = `Exists ([t], c) in
              `Let ([[], c, IdentMap.empty], c2)
          | _ ->
              raise_error (NotImplemented ("some structure item", pstr_loc))
      in
      let default_bindings =
        let plus_scheme =
          let plus_var = fresh_type_var ~letter:'z' () in
          let plus_type =
            type_cons_arrow type_cons_int (type_cons_arrow type_cons_int type_cons_int)
          in
          let pos = Location.none in
          let plus_map = IdentMap.add (ident "+" pos) plus_var IdentMap.empty in
          [plus_var], `Equals (plus_var, plus_type), plus_map
        in
        let mult_scheme =
          let mult_var = fresh_type_var ~letter:'z' () in
          let mult_type =
            type_cons_arrow type_cons_int (type_cons_arrow type_cons_int type_cons_int)
          in
          let pos = Location.none in
          let mult_map = IdentMap.add (ident "*" pos) mult_var IdentMap.empty in
          [mult_var], `Equals (mult_var, mult_type), mult_map
        in
        [plus_scheme; mult_scheme]
      in
      let topmost_constraint =
        List.fold_right generate_constraint_structure_item structure `Dump
      in
      if opt_default_bindings then
        `Let (default_bindings, topmost_constraint)
      else
        topmost_constraint

  (* Useful for let pattern = expression ... *)
  and generate_constraint_pat_expr: pattern * expression -> type_var list * type_constraint * type_var IdentMap.t =
    fun (pat, expr) ->
      let x = fresh_type_var ~letter:'x' () in
      let c1, var_map, generated_vars = generate_constraint_pattern x pat in
      let c1' = generate_constraint_expression x expr in
      let konstraint = `Exists (generated_vars, `Conj (c1, c1')) in
      [x], konstraint, var_map

  in

  (** The "driver" for OCaml constraint generation. Takes care of catching all
      errors and returning an understandable error message. *)
  try
    `Ok (generate_constraint structure)
  with
    | Error e -> `Error e
    | Algebra.Error e -> `Error (AlgebraError e)

let string_of_error =
  let print_loc () { Location.loc_start; Location.loc_end; Location.loc_ghost } =
    let open Lexing in
    assert (not loc_ghost);
    let { pos_fname; pos_lnum; pos_bol; _ } = loc_start in
    let { pos_bol = pos_end; _ } = loc_end in
    Printf.sprintf "File %s, line %d, characters %d-%d"
      pos_fname pos_lnum pos_bol pos_end
  in function
  | NotImplemented (r, loc) ->
      Printf.sprintf
        "%a: the following OCaml feature is not implemented: %s\n"
        print_loc loc r
  | VariableBoundSeveralTimes (v, loc) ->
      Printf.sprintf
        "%a: variable %s is bound several times in the matching\n"
        print_loc loc v
  | VariableMustOccurBothSides (v, loc) ->
      Printf.sprintf
        "%a: variable %s must occur on both sides of this pattern\n"
        print_loc loc v
  | AlgebraError e ->
      Algebra.string_of_error e
