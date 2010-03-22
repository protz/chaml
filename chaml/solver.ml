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

type solver_state = solver_stack * unification_constraint * type_constraint

let solve: type_constraint -> TypedAst.t = fun konstraint ->
  let rec analyze: unification_env -> solver_state -> solver_state =
    fun unification_env solver_state ->
    let solver_stack, unification_constraint, type_constraint = solver_state in
    match type_constraint with
      | `True ->
          move_into unification_env solver_state
      | `Equals (t1, t2) ->
          let t1 = uterm_of_tterm unification_env t1 in
          let t2 = uterm_of_tterm unification_env t2 in
          let konstraint =
            unify_terms unification_env t1 t2 unification_constraint
          in
          let new_state = solver_stack, konstraint, type_constraint in
          analyze unification_env new_state
      | _ ->
          assert false
  and move_into: unification_env -> solver_state -> solver_state =
    fun unification_env solver_state ->
    let solver_stack, unification_constraint, type_constraint = solver_state in
    assert false
  in
  let initial_state: solver_state = `Empty, `True, konstraint in
  let initial_env = {
    current_rank = 0;
    pools = [];
    tvar_to_uvar = Hashtbl.create 64
  } in
  match analyze initial_env initial_state with
    | `Empty, knowledge, `True -> ()
    | _ -> assert false
