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
          let t1 = uvar_of_tterm unifier_env (tv_tt t1) in
          let t2 = uvar_of_tterm unifier_env t2 in
          Error.debug "[SE] %s = %s\n" (uvar_name t1) (uvar_name t2);
          unify unifier_env t1 t2;
          unifier_env
      | `Instance (ident, t) ->
          (* For instance: ident = f (with let f x = x), and t = int -> int *)
          (* scheme is basically what came out of solving the left branch of the
           * let. young_vars is all the young variables that are possibly
           * quantified inside that scheme *)
          let young_vars, scheme_uvar =
            IdentMap.find ident unifier_env.scheme_of_ident
          in
          let desc = UnionFind.find scheme_uvar in
          let t_uvar = uvar_of_tterm unifier_env (tv_tt t) in
          if desc.rank >= current_rank unifier_env then begin
            Error.debug "[S-Old] Not generalizing\n";
            unify unifier_env scheme_uvar t_uvar;
            unifier_env
          end else begin
            Error.debug "[S-Young] Generalizing\n";
            let instance = fresh_copy unifier_env scheme_uvar in
            unify unifier_env instance t_uvar;
            unifier_env
          end
      | `Conj (c1, c2) ->
          (* Given that analyze returns the environment with the same pool it
           * was given, we can forward the environment throughout the calls. *)
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
          (* We take all the schemes, and schedule them for execution. *)
          schedule_schemes unifier_env schemes c2
      | `Dump ->
          unifier_env
  (* This one only implements scheduling and merging multiple simultaneous let
   * definitions. This roughly corresponds to S-SOLVE-LET. *)
  and schedule_schemes: unifier_env -> type_scheme list -> type_constraint -> unifier_env =
    fun unifier_env schemes c ->
      (* This auxiliary function 
       * - solves the constraint
       * - generalizes variables as needed
       * - associates schemes to identifiers in the environment
       * *)
      let solve_branch: unifier_scheme IdentMap.t -> type_scheme -> unifier_scheme IdentMap.t =
        fun new_map scheme ->
        Error.debug "[SL] Solving scheme\n";
        let sub_env = step_env unifier_env in
        let vars, konstraint, var_map = scheme in
        (* This makes sure all the universally quantified variables appear in
         * the Pool. *)
        Jlist.ignore_map
          (uvar_of_tterm unifier_env)
          (vars: type_var list :> type_term list);
        (* Solve the constraint in the scheme. *)
        let _unifier_env' =
          analyze (sub_env, konstraint)
        in
        (* A young variable is a variable that hasn't been unified with a
         * variable defined before. *)
        let is_young uvar =
          let desc = UnionFind.find uvar in
          assert (desc.rank <= current_rank sub_env);
          desc.rank = current_rank sub_env
        in
        let current_pool = current_pool sub_env in
        (* We can just get rid of the old vars: they have been unified with a
         * var that's already in its own pool, with a lower rank. *)
        let young_vars = List.filter is_young current_pool.Pool.members in
        (* Each identifier is assigned a scheme. It's a list of the young vars
         * and a pointer to a variable that contains the constraint associated
         * to the identifier. *)
        let assign_scheme ident =
          let uvar = uvar_of_tterm unifier_env (tv_tt (IdentMap.find ident var_map)) in
          young_vars, uvar
        in
        IdentMap.fold
          (fun ident type_var map ->
            IdentMap.add ident (assign_scheme ident) map)
          (var_map: type_var IdentMap.t :> type_term IdentMap.t)
          new_map
      in
      let new_map =
        List.fold_left solve_branch unifier_env.scheme_of_ident schemes
      in
      Error.debug "[SR] Moving to the right branch\n";
      let new_state = { unifier_env with scheme_of_ident = new_map }, c in
      analyze new_state
  in
  let initial_env = {
    current_pool = Pool.base_pool;
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
  let print_type: ident -> unifier_scheme -> unit =
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
                      Printf.sprintf "(%s → %s)" t1 t2
                    else
                      Printf.sprintf "%s → %s" t1 t2
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
      let _, uvar = scheme in
      let ident = ConstraintPrinter.string_of_ident ident in
      c := 0;
      Printf.printf "val %s: %s\n" ident (print_type false uvar)
  in
  flush stderr;
  flush stdout;
  IdentMap.iter print_type knowledge.scheme_of_ident
