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

type solver_stack_elt = [
  | `Conj of type_constraint
  | `LetRight of unifier_scheme
  | `LetLeft of type_scheme list * type_constraint
]
type solver_stack = solver_stack_elt list

type solver_state = solver_stack * unifier_env * type_constraint

let solve: type_constraint -> TypedAst.t = fun konstraint ->
  let rec analyze: solver_state -> solver_state =
    fun solver_state ->
    let solver_stack, unifier_env, type_constraint = solver_state in
    match type_constraint with
      | `True ->
          move_into solver_state
      | `Equals (t1, t2) ->
          let t1 = uvar_of_tterm unifier_env (t1: type_var :> type_term) in
          let t2 = uvar_of_tterm unifier_env t2 in
          unify unifier_env t1 t2;
          analyze solver_state
      | `Instance (ident, t) ->
          (* Clarify this case once I know how the stack is handled below.
          * Important: beware of Identifier not found!  *)
          assert false
      | `Conj (c1, c2) ->
          let solver_stack = `Conj c1 :: solver_stack in
          let solver_state = solver_stack, unifier_env, c2 in
          analyze solver_state
      | `Exists (xis, c) ->
          (* This makes sure we add the existentially defined variables as
           * universally quantified in the currently enclosing let definition.
           * *)
          Jlist.ignore_map
            (uvar_of_tterm unifier_env)
            (xis: type_var list :> type_term list);
          let solver_state = solver_stack, unifier_env, c in
          analyze solver_state
      | `Let (schemes, c2) ->
          (* We're under a new let, so variables from now on are universally
           * quantified for this rank. *)
          let new_env = step_env unifier_env in
          (* We take all the schemes, and schedule them for execution. *)
          let front = `LetLeft (schemes, c2) in
          let new_state = front :: solver_stack, new_env, `True in
          Error.debug "ping -";
          schedule_schemes new_state
          (* Itérer sur les identifiants définis à ce niveau, générer une
           * variable de type, l'ajouter à la pool (pour quand on descendra dans
           * e2). En revanche, ne *PAS* ajouter les identifiants à la IdentMap,
           * ça se fera au moment de sauter dans la branche droit du let (e2).
           * *)
      | `Dump ->
          solver_state
  (* This one only implements scheduling and merging multiple simultaneous let
   * definitions. This roughly corresponds to S-SOLVE-LET. *)
  and schedule_schemes: solver_state -> solver_state =
    fun solver_state ->
    let solver_stack, unifier_env, type_constraint = solver_state in
    assert (type_constraint = `True);
    Error.debug "pong\n";
    match solver_stack with
      | `LetLeft (schemes, c) :: rest ->
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
            Jlist.ignore_map
              (uvar_of_tterm unifier_env)
              (vars: type_var list :> type_term list);
            let _solver_stack', _unifier_env', type_constraint' =
              analyze (solver_stack, unifier_env, konstraint)
            in
            assert (type_constraint' = `True);
            Error.debug "pong\n";
            IdentMap.fold
              (fun ident type_var map ->
                IdentMap.add ident (uvar_of_tterm unifier_env type_var) map)
              (var_map: type_var IdentMap.t :> type_term IdentMap.t)
              new_map
          in
          let new_map =
            List.fold_left solve_branch unifier_env.ident_to_uvar schemes
          in
          (* Actually we're already doing S-POP-ENV *)
          let new_state =
            rest, { unifier_env with ident_to_uvar = new_map }, c
          in
          analyze new_state
      | _ ->
          assert false
  and move_into: solver_state -> solver_state =
    fun solver_state ->
    let solver_stack, unifier_env, type_constraint = solver_state in
    assert (type_constraint = `True);
    match solver_stack with
      | `Conj c :: rest ->
          let new_state = rest, unifier_env, c in
          analyze new_state
      | `LetLeft _ :: _ ->
          (* We hand back the control flow to schedule_schemes. *)
          Error.debug "ping - ";
          solver_state
      | _ ->
          failwith "Not implemented"
  in
  let initial_env = {
    pools = [Pool.base_pool];
    tvar_to_uvar = Hashtbl.create 64;
    ident_to_uvar = IdentMap.empty;
  } in
  let initial_state: solver_state = [], initial_env, konstraint in
  match analyze initial_state with
    | [], knowledge, `True -> ()
    | _ -> assert false
