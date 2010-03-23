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

type solver_scheme = unification_var generic_scheme
type solver_constraint = unification_var generic_constraint

type solver_stack = [
  | `Empty
  | `Conj of solver_stack * solver_constraint
  | `Let of solver_stack * solver_scheme
]

type solver_state = solver_stack * unification_env * type_constraint

let solve: type_constraint -> TypedAst.t = fun konstraint ->
  let rec analyze: solver_state -> solver_state =
    fun solver_state ->
    let _solver_stack, unification_env, type_constraint = solver_state in
    match type_constraint with
      | `True ->
          move_into solver_state
      | `Equals (t1, t2) ->
          let t1 = uterm_of_tterm unification_env (t1: type_var :> type_term) in
          let t2 = uterm_of_tterm unification_env t2 in
          unify unification_env t1 t2;
          analyze solver_state
      | _ ->
          assert false
  and move_into: solver_state -> solver_state =
    fun solver_state ->
    let _solver_stack, _unification_env, _type_constraint = solver_state in
    assert false
  in
  let initial_env = {
    current_rank = 0;
    pools = [];
    tvar_to_uvar = Hashtbl.create 64
  } in
  let initial_state: solver_state = `Empty, initial_env, konstraint in
  match analyze initial_state with
    | `Empty, knowledge, `True -> ()
    | _ -> assert false
