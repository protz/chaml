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

type error =
  | UnifyError of Unify.error

exception Error of error

let string_of_error = function
  | UnifyError e ->
      Unify.string_of_error e

let unify_or_raise unifier_env t1 t2 =
  match (unify unifier_env t1 t2) with
  | `Ok -> ();
  | `Error e -> raise (Error (UnifyError e))

let solve =
  fun ~caml_types:opt_caml_types ~print_types:opt_print_types konstraint ->

  let rec analyze: unifier_env -> type_constraint -> unifier_env =
    fun unifier_env type_constraint ->
    match type_constraint with
      | `True ->
          Error.debug "[STrue] Returning from True\n";
          unifier_env
      | `Equals (t1, t2) ->
          let t1 = uvar_of_tterm unifier_env (tv_tt t1) in
          let t2 = uvar_of_tterm unifier_env t2 in
          Error.debug "[SEquals] %a = %a\n" uvar_name t1 uvar_name t2;
          unify_or_raise unifier_env t1 t2;
          unifier_env
      | `Instance (ident, t) ->
          (* For instance: ident = f (with let f x = x), and t = int -> int *)
          (* scheme is basically what came out of solving the left branch of the
           * let. young_vars is all the young variables that are possibly
           * quantified inside that scheme *)
          let t_uvar = uvar_of_tterm unifier_env (tv_tt t) in
          Error.debug "[SInstance] taking an instance of %s\n" (string_of_ident ident);
          let scheme = IdentMap.find ident unifier_env.scheme_of_ident in
          let young_vars, scheme_uvar = scheme in
          let scheme_desc = UnionFind.find scheme_uvar in
          let ident_s = string_of_ident ident in
          if scheme_desc.rank < current_rank unifier_env then begin
            let instance = fresh_copy unifier_env scheme in
            Error.debug
              "[SCopy] %a is a copy of %a\n" uvar_name instance uvar_name scheme_uvar;
            Error.debug
              "[S-Old] Taking an instance of %s: %a\n" ident_s uvar_name instance;
            unify_or_raise unifier_env instance t_uvar;
            unifier_env
          end else begin
            Error.debug "[S-Young] Unifying %s directly\n" ident_s;
            unify_or_raise unifier_env scheme_uvar t_uvar;
            unifier_env
          end
      | `Conj (c1, c2) ->
          (* Do *NOT* forward _unifier_env! Identifiers in c1's scope must not
           * go through c2's scope, this would be fatal. *)
          let _unifier_env = analyze unifier_env c2 in
          analyze unifier_env c1
      | `Exists (xis, c) ->
          (* This makes sure we add the existentially defined variables as
           * universally quantified in the currently enclosing let definition.
           * *)
          Jlist.ignore_map
            (uvar_of_tterm unifier_env)
            (xis: type_var list :> type_term list);
          analyze unifier_env c
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
        let vars, konstraint, var_map = scheme in
        (* --- Debug --- *)
        let module JIM = Jmap.Make(IdentMap) in
        let idents = JIM.keys var_map in
        let idents = List.map string_of_ident idents in
        let idents = String.concat ", " idents in
        Error.debug_simple
          (Bash.color 219 "[SLeft] Solving scheme for %s\n" idents);
        (* --- End Debug --- *)

        let sub_env = step_env unifier_env in
        (* This makes sure all the universally quantified variables appear in
         * the Pool. *)
        Jlist.ignore_map
          (uvar_of_tterm unifier_env)
          (vars: type_var list :> type_term list);

        (* Solve the constraint in the scheme. *)
        let _unifier_env' =
          analyze sub_env konstraint
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
        (* Filter out duplicates *)
        let young_vars =
          Jlist.remove_duplicates
            ~hash_func:(fun x -> Hashtbl.hash (UnionFind.find x))
            ~equal_func:UnionFind.equivalent
            young_vars
        in
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
      Error.debug "[SRight] Moving to the right branch\n";
      let new_env = { unifier_env with scheme_of_ident = new_map } in
      analyze new_env c
  in
  let initial_env = {
    current_pool = Pool.base_pool;
    uvar_of_tterm = Hashtbl.create 64;
    scheme_of_ident = IdentMap.empty;
  } in
  try
    let knowledge = analyze initial_env konstraint in
    let module JIM = Jmap.Make(IdentMap) in
    let kv = JIM.to_list knowledge.scheme_of_ident in
    let kv = List.filter (fun ((_, pos), _) -> not pos.Location.loc_ghost) kv in
    let kv = List.sort (fun ((_, pos), _) ((_, pos'), _) -> compare pos pos') kv in
    let print_kv (ident, scheme) =
      let ident = string_of_ident ident in
      let s = string_of_scheme ~caml_types:opt_caml_types ident scheme in
      print_endline s
    in
    flush stderr;
    if opt_print_types then
      List.iter print_kv kv;
    `Ok ()
  with
    Error e -> `Error e
