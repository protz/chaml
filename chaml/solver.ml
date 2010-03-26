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
  let rec analyze: solver_state -> unifier_env =
    fun solver_state ->
    let unifier_env, type_constraint = solver_state in
    match type_constraint with
      | `True ->
          Error.debug "[ST] Returning from True\n";
          unifier_env
      | `Equals (t1, t2) ->
          let t1 = uvar_of_tterm unifier_env (t1: type_var :> type_term) in
          let t2 = uvar_of_tterm unifier_env t2 in
          Error.debug "[SE] %s = %s\n" (uvar_name t1) (uvar_name t2);
          unify unifier_env t1 t2;
          unifier_env
      | `Instance (ident, t) ->
          (* We need to get the constraint associated to ident *)
          let scheme = IdentMap.find ident unifier_env.scheme_of_ident in
          let vars, konstraint, var_map = scheme in
          (* ident vas previously bound to old_tvar *)
          let old_tvar = IdentMap.find ident var_map in
          (* That is, was represented as old_uvar for the unifier **)
          let old_uvar = Hashtbl.find unifier_env.uvar_of_tvar old_tvar in
          (* We make a copy of that constraint, i.e. we "instanciate" the scheme *)
          let mapping, konstraint = fresh_copy konstraint in
          (* And we translate the old vars to new ones for the instance *)
          let vars = List.map (Hashtbl.find mapping) vars in
          (* We solve that constraint *)
          let unifier_env = analyze (unifier_env, `Exists (vars, konstraint)) in
          let new_uvar = match Jhashtbl.find_opt mapping old_tvar with
            (* The variable wasn't quantified in the scheme so it's not
             * necessary to duplicate it *)
            | None ->
                Error.debug "[CD] Variable %s was NOT quantified in the scheme\n" (uvar_name old_uvar);
                old_uvar
            (* There is now a fresh type variable for ident *)
            | Some new_tvar ->
                let new_uvar = Hashtbl.find unifier_env.uvar_of_tvar new_tvar in
                Error.debug "[CD] Variable %s was quantified in the scheme\n" (uvar_name new_uvar);
                new_uvar
          in
          (* So we unify the two. Useless if None above. *)
          unify unifier_env old_uvar new_uvar;
          (* And make sure we unify the subvar with the term we instanciate to *)
          let tterm = uvar_of_tterm unifier_env (t: type_var :> type_term) in
          unify unifier_env new_uvar tterm;
          (* We're done! *)
          unifier_env
      | `Conj (c1, c2) ->
          let unifier_env = analyze (unifier_env, c2) in
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
          unifier_env
  (* This one only implements scheduling and merging multiple simultaneous let
   * definitions. This roughly corresponds to S-SOLVE-LET. *)
  and schedule_schemes: unifier_env -> type_scheme list -> type_constraint -> unifier_env =
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
      let solve_branch new_map scheme =
        Error.debug "[SL] Solving scheme\n";
        let vars, konstraint, var_map = scheme in
        (* Making sure we register the universally quantified variables in the
         * right pool. *)
        Jlist.ignore_map
          (uvar_of_tterm unifier_env)
          (vars: type_var list :> type_term list);
        (* Solve the constraint in the scheme. This basically forbids
         * let x = string_of_int 2. in 2 *)
        let _unifier_env' =
          analyze (unifier_env, konstraint)
        in
        (* Register in the map all the identifiers that have been bound in that
         * scheme so that we can get back to this scheme later. *)
        IdentMap.fold
          (fun ident type_var map ->
            IdentMap.add ident scheme map)
          (var_map: type_var IdentMap.t :> type_term IdentMap.t)
          new_map
      in
      let new_map =
        List.fold_left solve_branch unifier_env.scheme_of_ident schemes
      in
      (* XXX Perform all generalizations here *)
      Error.debug "[SR] Moving to the right branch\n";
      let new_state = { unifier_env with scheme_of_ident = new_map }, c in
      analyze new_state
  in
  let initial_env = {
    pools = [Pool.base_pool];
    uvar_of_tvar = Hashtbl.create 64;
    scheme_of_ident = IdentMap.empty;
  } in
  let initial_state: solver_state = initial_env, konstraint in
  let c = ref 0 in
  let fresh_greek_var =
    let alpha = 0xB0 in
    fun () ->
      c := !c + 1;
      if (!c > 24) then Error.fatal_error "Out of Greek letters!\n";
      String.concat "" [
        "\xCE";
        String.make 1 (char_of_int (alpha + !c));
      ]
  in
  let knowledge = analyze initial_state in 
  let print_type: ident -> type_scheme -> unit =
    fun ident scheme ->
      let greek_of_repr = Hashtbl.create 24 in
      let rec print_type paren uvar =
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
              begin match cons_name with
                | { cons_name = "->" } ->
                    let t1 = print_type true (List.nth cons_args 0) in
                    let t2 = print_type false (List.nth cons_args 1) in
                    if paren then
                      Printf.sprintf "(%s -> %s)" t1 t2
                    else
                      Printf.sprintf "%s -> %s" t1 t2
                | { cons_name = "*" } ->
                    let types = List.map (print_type true) cons_args in
                    Printf.sprintf "(%s)" (String.concat " * " types)
                | { cons_name; } ->
                    let types = List.map (print_type true) cons_args in
                    let args = String.concat ", " types in
                    if List.length types > 0 then
                      Printf.sprintf "(%s (%s))" cons_name args
                    else
                      Printf.sprintf "%s" cons_name
              end
      in
      let _, _, tvar_of_ident = scheme in
      let tvar = IdentMap.find ident tvar_of_ident in
      let uvar = Hashtbl.find knowledge.uvar_of_tvar tvar in
      let ident = ConstraintPrinter.string_of_ident ident in
      c := 0;
      Printf.printf "val %s: %s\n" ident (print_type false uvar)
  in
  flush stderr;
  flush stdout;
  IdentMap.iter print_type knowledge.scheme_of_ident
