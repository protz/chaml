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
open Unify
open Constraint

type solver_scheme = unifier_var generic_scheme
type solver_constraint = unifier_var generic_constraint
type solver_state = unifier_env * type_constraint

(* We try to enforce many invariants. When we arrive at a leaf of the calls, we
 * return iff the constraint is `True. *)
let solve: type_constraint -> TypedAst.t = fun konstraint ->
  let rec analyze: solver_state -> solver_state =
    fun solver_state ->
    let unifier_env, type_constraint = solver_state in
    match type_constraint with
      | `True ->
          Error.debug "[ST] Returning from True\n";
          solver_state
      | `Equals (t1, t2) ->
          let t1 = uvar_of_tterm unifier_env (t1: type_var :> type_term) in
          let t2 = uvar_of_tterm unifier_env t2 in
          Error.debug "[SE] %s = %s\n" (uvar_name t1) (uvar_name t2);
          unify unifier_env t1 t2;
          analyze (unifier_env, `True)
      | `Instance (ident, t) ->
          let t1 = IdentMap.find ident unifier_env.ident_to_uvar in
          let t2 = uvar_of_tterm unifier_env (t: type_var :> type_term) in
          (* let t2 = fresh_copy unifier_env t2 in *)
          Error.debug "[SI] %s < %s\n" (uvar_name t1) (uvar_name t2);
          unify unifier_env t1 t2;
          unifier_env, `True
      | `Conj (c1, c2) ->
          let unifier_env, c = analyze (unifier_env, c2) in
          assert (c = `True);
          analyze (unifier_env, c1)
      | `Exists (xis, c) ->
          (* This makes sure we add the existentially defined variables as
           * universally quantified in the currently enclosing let definition.
           * *)
          Jlist.ignore_map
            (uvar_of_tterm unifier_env)
            (xis: type_var list :> type_term list);
          let solver_state = unifier_env, c in
          analyze solver_state
      | `Let (schemes, c2) ->
          (* We're under a new let, so variables from now on are universally
           * quantified for this rank. *)
          let new_env = step_env unifier_env in
          (* We take all the schemes, and schedule them for execution. *)
          schedule_schemes new_env schemes c2
      | `Dump ->
          solver_state
  (* This one only implements scheduling and merging multiple simultaneous let
   * definitions. This roughly corresponds to S-SOLVE-LET. *)
  and schedule_schemes: unifier_env -> type_scheme list -> type_constraint -> solver_state =
    fun unifier_env schemes c ->
      (* This auxiliary function 
       * - adds the universally quantified type variables into the pool
       * - schedules the scheme's * constraint
       * - adds the identifier to new_map and moves on to the next
       * constraint
       *
       * Please note that the return value is not taken into account at all,
       * only after all the solve_branches have been called is it used.
       * *)
      let solve_branch new_map (vars, konstraint, var_map) =
        Error.debug "[SL] Solving scheme\n";
        Jlist.ignore_map
          (uvar_of_tterm unifier_env)
          (vars: type_var list :> type_term list);
        let _unifier_env', type_constraint' =
          analyze (unifier_env, konstraint)
        in
        assert (type_constraint' = `True);
        IdentMap.fold
          (fun ident type_var map ->
            IdentMap.add ident (uvar_of_tterm unifier_env type_var) map)
          (var_map: type_var IdentMap.t :> type_term IdentMap.t)
          new_map
      in
      let new_map =
        List.fold_left solve_branch unifier_env.ident_to_uvar schemes
      in
      (* XXX Perform all generalizations here *)
      Error.debug "[SR] Moving to the right branch\n";
      let new_state = { unifier_env with ident_to_uvar = new_map }, c in
      analyze new_state
  in
  let initial_env = {
    pools = [Pool.base_pool];
    tvar_to_uvar = Hashtbl.create 64;
    ident_to_uvar = IdentMap.empty;
  } in
  let initial_state: solver_state = initial_env, konstraint in
  let fresh_greek_var =
    let c = ref 0 in
    let alpha = 0xB0 in
    fun () ->
      c := !c + 1;
      if (!c > 24) then Error.fatal_error "Out of Greek letters!\n";
      String.concat "" [
        "\xCE";
        String.make 1 (char_of_int (alpha + !c));
      ]
  in
  let print_type: ident -> unifier_var -> unit =
    let greek_of_repr = Hashtbl.create 24 in
    let rec print_type uvar =
      let repr = UnionFind.find uvar in
      match repr.term with
        | None ->
            begin match Jhashtbl.find_opt greek_of_repr repr with
              | None -> 
                  let letter = fresh_greek_var () in
                  Hashtbl.add greek_of_repr repr letter;
                  letter
              | Some letter ->
                  letter
            end
        | Some (`Cons (cons_name, cons_args)) ->
            let types = List.map print_type cons_args in
            begin match cons_name with
              | { cons_name = "->" } ->
                  let t1 = List.nth types 0 in
                  let t2 = List.nth types 1 in
                  Printf.sprintf "%s -> %s" t1 t2
              | { cons_name = "*" } ->
                  String.concat " * " types
              | { cons_name; } ->
                  let args = String.concat ", " types in
                  if List.length types > 0 then
                    Printf.sprintf "%s (%s)" cons_name args
                  else
                    Printf.sprintf "%s" cons_name
            end
    in
    fun ident uvar ->
      let ident = ConstraintPrinter.string_of_ident ident in
      Printf.printf "val %s: %s\n" ident (print_type uvar)
  in
  match analyze initial_state with
    | knowledge, `Dump ->
        flush stderr;
        flush stdout;
        IdentMap.iter print_type knowledge.ident_to_uvar
    | _ -> assert false
