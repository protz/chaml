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

let propagate_ranks uvar =
  let seen = Hashtbl.create 64 in
  let rec propagate_ranks: int -> unifier_var -> int = fun parent_rank uvar ->
    let repr = UnionFind.find uvar in
    (* Top-down *)
    if parent_rank < repr.rank then
      repr.rank <- parent_rank;
    match repr.term with
      | None ->
          repr.rank
      | Some (`Cons (cons_name, cons_args)) ->
          (* Bottom-up *)
          let ranks = List.map (dont_loop repr.rank) cons_args in
          let max_rank = Jlist.max ranks in
          if max_rank < repr.rank && List.length cons_args > 0 then
            repr.rank <- max_rank;
          repr.rank
  and dont_loop rank uvar =
    if Hashtbl.mem seen uvar then
      (UnionFind.find uvar).rank
    else begin
      Hashtbl.add seen uvar ();
      propagate_ranks rank uvar
    end
  in
  let repr = UnionFind.find uvar in
  ignore (dont_loop repr.rank uvar)


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
          Error.debug "[SEquals] %s = %s\n" (UnionFind.find t1).name (UnionFind.find t2).name;
          unify_or_raise unifier_env t1 t2;
          unifier_env
      | `Instance (ident, t) ->
          (* For instance: ident = f (with let f x = x), and t = int -> int *)
          (* scheme is basically what came out of solving the left branch of the
           * let. young_vars is all the young variables that are possibly
           * quantified inside that scheme *)
          let t_uvar = uvar_of_tterm unifier_env (tv_tt t) in
          let scheme = IdentMap.find ident unifier_env.scheme_of_ident in
          let ident_s = string_of_ident ident in
          let instance = fresh_copy unifier_env scheme in
          Error.debug
              "[SInstance] Taking an instance of %s: %a\n" ident_s uvar_name instance;
          unify_or_raise unifier_env instance t_uvar;
          unifier_env
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

        (* Create a fresh environment to type the left part in it. This also
         * allows us to create a fresh pool which will contain all the
         * existentially quantified variables in it. *)
        let sub_env = step_env unifier_env in

        (* Solve the constraint in the scheme. *)
        let _unifier_env' =
          analyze sub_env konstraint
        in
        let current_pool = current_pool sub_env in

        (* Debug *)
        let debug_inpool l =
          let rank = current_rank sub_env in
          let members =
            List.map
              (fun x ->
                 let repr = (UnionFind.find x) in
                   Printf.sprintf "%s(%d)" repr.name repr.rank)
              l
          in
          Error.debug_simple (Bash.color 208 "[InPool] %d: %s\n" rank (String.concat ", " members));
        in

        (* We want to keep "young" variables that have been introduced while
         * solving the constraint attached to that branch. We don't want to
         * quantify over variables that represent constructors, that's useless. *)
        let is_young uvar =
          let desc = UnionFind.find uvar in
          assert (desc.rank <= current_rank sub_env);
          desc.rank = current_rank sub_env && desc.term = None
        in
        let young_vars = current_pool.Pool.members in

        (* Filter out duplicates. This isn't necessary but still this should
         * speed things up. *)
        let young_vars =
          Jlist.remove_duplicates
            ~hash_func:(fun x -> Hashtbl.hash (UnionFind.find x))
            ~equal_func:UnionFind.equivalent
            young_vars
        in

        (* See lemma 10.6.7 in ATTAPL. This is needed. *)
        debug_inpool young_vars;
        List.iter propagate_ranks young_vars;

        (* We can just get rid of the old vars: they have been unified with a
         * var that's already in its own pool, with a lower rank. *)
        let young_vars = List.filter is_young young_vars in

        debug_inpool young_vars;

        (* Each identifier is assigned a scheme. It's a list of the young vars
         * and a pointer to a variable that contains the constraint associated
         * to the identifier. *)
        let assign_scheme ident =
          let uvar = uvar_of_tterm unifier_env (tv_tt (IdentMap.find ident var_map)) in
          young_vars, uvar
        in
        IdentMap.fold
          (fun ident type_var map ->
             let r = IdentMap.add ident (assign_scheme ident) map in
             let string_of_key = fun x -> x.name in
             Error.debug_simple
               (Bash.color
                  185
                  "[SScheme] Got %s\n"
                  (string_of_scheme ~string_of_key
                     (string_of_ident ident) (IdentMap.find ident r)));
             r
          )
          (var_map: type_var IdentMap.t :> type_term IdentMap.t)
          new_map
      in
      let new_map =
        List.fold_left solve_branch unifier_env.scheme_of_ident schemes
      in
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
    Hashtbl.iter
      (fun k v -> Error.debug "[Rank] %s: %d\n"
                    (UnionFind.find v).name
                    (UnionFind.find v).rank)
      knowledge.uvar_of_tterm;
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
