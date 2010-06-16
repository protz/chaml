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

open Unify
module BaseSolver = Unify.BaseSolver

module Constraint_ = Constraint.Make(BaseSolver) open Constraint_
open Algebra.Identifiers
open Algebra.Core

type error =
  | UnifyError of Unify.error
  | UnboundIdentifier of ident
  | MalformedConstraint
  | CyclicType

exception Error of error
let raise_error x = raise (Error x)

let string_of_error = function
  | UnifyError e ->
      Unify.string_of_error e
  | UnboundIdentifier i ->
      Printf.sprintf "Unbound identifier %s\n" (string_of_ident i)
  | CyclicType ->
      "Recursive types detected. Please use --enable recursive-types if \
       intended\n"
  | MalformedConstraint ->
      "The generated constraint has no ending. Who are you?\n"

let unify_or_raise unifier_env uvar1 uvar2 =
  match (unify unifier_env uvar1 uvar2) with
  | `Ok -> ();
  | `Error e -> raise_error (UnifyError e)

(* This function runs a DFS when we exit the left branch of a [`Let]. It takes
 * care of:
 * - propagating ranks
 * - marking variables on the fly and detecting cycles (if recursive types are
 * disabled)
 * *)
let run_dfs ~occurs_check young_vars =
  let seen = Uhashtbl.create 64 in
  let rec propagate_ranks: int -> descriptor -> int = fun parent_rank repr ->
    (* Top-down *)
    if parent_rank < repr.rank then
      repr.rank <- parent_rank;
    match repr.term with
      | None ->
          assert (repr.rank >= 0);
          repr.rank
      | Some (`Cons (_cons_name, cons_args)) ->
          (* Bottom-up *)
          let ranks = List.map (dont_loop repr.rank) cons_args in
          let max_rank = Jlist.max ranks in
          (* The result of Jlist.max is undefined when the list is empty *)
          if max_rank < repr.rank && List.length cons_args > 0 then
            repr.rank <- max_rank;
          repr.rank
  and dont_loop rank uvar =
    let repr = find uvar in
    match Uhashtbl.find_opt seen repr with
    | Some false ->
        repr.rank
    | Some true ->
        if (occurs_check) then
          raise_error (CyclicType)
        else
          repr.rank
    | None ->
        Uhashtbl.add seen repr true;
        let r = propagate_ranks rank repr in
        Uhashtbl.replace seen repr false;
        r
  in
  let f uvar =
    let repr = find uvar in
    ignore (dont_loop repr.rank uvar);
    assert (repr.rank >= 0)
  in
  List.iter f young_vars;
  seen

(* Some useful debug helpers *)
let debug_which_schemes buf var_map =
  let idents = IdentMap.keys var_map in
  let idents = List.map string_of_ident idents in
  let idents = String.concat ", " idents in
  Buffer.add_string buf (Bash.color 219 "[SLeft] Solving scheme for %s\n" idents)

let debug_inpool buf (prev_ranks, l, sub_env) =
  let rank = current_rank sub_env in
  let members = match prev_ranks with
    | None ->
        List.map
          (fun x ->
             let repr = find x in
               Printf.sprintf "%s(%d)" repr.name repr.rank)
          l
    | Some ranks ->
        List.map2
          (fun var old_rank ->
            let repr = find var in
            if old_rank <> repr.rank then
              Bash.color 42 "%s(%d)" repr.name repr.rank
            else
              Printf.sprintf "%s(%d)" repr.name repr.rank)
          l ranks
  in
  let str = Bash.color 208 "[InPool] %d: %s\n" rank (String.concat ", " members) in
  Buffer.add_string buf str

let debug_scheme buf (scheme, ident) =
  let scheme_str = string_of_scheme
    ~debug:()
    (string_of_ident ident)
    scheme
  in
  let str = Bash.color 185 "[SScheme] Got %s\n" scheme_str in
  Buffer.add_string buf str

let sort_global young_vars =
  let c x y = id x - id y in
  let young_vars = List.sort c young_vars in
  young_vars


exception Done of unifier_scheme IdentMap.t

let solve =
  fun ~caml_types:opt_caml_types
    ~print_types:opt_print_types
    ~recursive_types:opt_recursive_types
    konstraint ->

  let rec analyze: unifier_env -> type_constraint -> unit =
    fun unifier_env type_constraint ->
    match type_constraint with
      | `Done ->
          raise (Done (get_scheme_of_ident unifier_env))
      | `True ->
          Error.debug "[STrue] Returning from True\n";
      | `Equals (`Var uvar1, t2) ->
          let uvar2 = uvar_of_term unifier_env t2 in
          Error.debug "[SEquals] %a = %a\n" uvar_name uvar1 uvar_name uvar2;
          unify_or_raise unifier_env uvar1 uvar2;
      | `Instance (ident, `Var uvar, solver_instance) ->
          (* For instance: ident = f (with let f x = x), and t = int -> int
           * scheme is basically what came out of solving the left branch of the
           * let. young_vars is all the young variables that are possibly
           * quantified inside that scheme *)
          let scheme =
            match IdentMap.find_opt ident (get_scheme_of_ident unifier_env) with
              | Some v ->
                v
              | None ->
                raise_error (UnboundIdentifier ident)
          in
          let ident_s = string_of_ident ident in
          let { scheme_var = instance }, young_vars =
            fresh_copy unifier_env scheme
          in
          Error.debug
              "[SInstance] Taking an instance of %s: %a\n" ident_s uvar_name instance;
          unify_or_raise unifier_env instance uvar;
          solver_instance := young_vars;
      | `Conj (c1, c2) ->
          (* Do *NOT* forward _unifier_env! Algebra.Identifiers in c1's scope must not
           * go through c2's scope, this would be fatal. *)
          analyze unifier_env c2;
          analyze unifier_env c1
      | `Exists (xis, c) ->
          (* This makes sure we add the existentially defined variables as
           * universally quantified within the currently enclosing let
           * definition.  *)
          List.iter (fun (`Var x) -> ensure_ready unifier_env x) xis;
          analyze unifier_env c
      | `Let (schemes, c2) ->
          (* We take all the schemes, and schedule them for execution. *)
          schedule_schemes unifier_env schemes c2
  (* This one only implements scheduling and merging multiple simultaneous let
   * definitions. This roughly corresponds to S-SOLVE-LET. *)
  and schedule_schemes: unifier_env -> type_scheme list -> type_constraint -> unit =
    fun unifier_env schemes c ->
      (* This auxiliary function
       * - solves the constraint
       * - generalizes variables as needed
       * - associates schemes to identifiers in the environment
       * *)
      let solve_branch: unifier_scheme IdentMap.t -> type_scheme -> unifier_scheme IdentMap.t =
        fun new_map scheme ->
        (* Create a fresh environment to type the left part in it. This also
         * allows us to create a fresh pool which will contain all the
         * existentially quantified variables in it. *)
        let sub_env = step_env unifier_env in
        let vars, konstraint, var_map, pscheme = scheme in
        Error.debug "%a" debug_which_schemes var_map;

        (* Make sure we register the variables that haven't been initialized yet
         * into the sub environment's pool. *)
        List.iter (fun (`Var uvar) -> ensure_ready sub_env uvar) vars;

        (* Solve the constraint in the scheme. *)
        Error.dinc ();
        analyze sub_env konstraint;
        Error.ddec ();
        let sub_pool = sub_pool unifier_env in
        let pool_vars = sub_pool.Pool.members in

        (* Filter out duplicates. This isn't necessary but still this should
         * speed things up. We maintain the invariant that each descriptor has
         * at least one unifier_var that points towards it either in a scheme or
         * in a pool. *)
        let pool_vars =
          let mark = Mark.fresh () in
          let t_list = ref [] in
          List.iter
            (fun x -> 
              let repr = find x in
              if not (Mark.same repr.mark mark) then begin
                t_list := x :: !t_list;
                repr.mark <- mark;
              end;
            )
          pool_vars;
          !t_list
        in
        let pool_vars = List.sort (fun a b -> rank a - rank b) pool_vars in

        (* This is rank propagation. See lemma 10.6.7 in ATTAPL. This is needed. *)
        Error.debug "%a" debug_inpool (None, pool_vars, sub_env);
        let prev_ranks = List.map rank pool_vars in
        let occurs_check = not opt_recursive_types in
        let _reachable = run_dfs ~occurs_check pool_vars in
        Error.debug "%a" debug_inpool (Some prev_ranks, pool_vars, sub_env);

        (* Young variables are marked as belonging to a scheme, they are
         * generalized. Old variables are sent back to their pools.
         *
         * We need to compute a list of variables that need to be quantified in
         * a scheme. For instance, some variables might be unreachable and we
         * don't schemes such as ∀ α. int. We first fill the [unreachable_vars]
         * hash table with all the variables that are universally bound in this
         * pool. Afterwards, we do a DFS that removes all the variables it can
         * reach starting from each identifier from unreachable_vars. What
         * remains in [unreachable_vars] is the universally quantified variables
         * that will never be instanciated, so we unify these with ⊥ (bottom). *)
        let current_rank = current_rank sub_env in
        let young_vars = List.filter
          (fun uvar ->
            let repr = find uvar in
            assert (repr.rank <= current_rank);
            (* Is it a young variable? *)
            if repr.rank = current_rank then begin
              repr.rank <- -1;
              repr.term = None
            end else begin
              let the_vars_pool = get_pool unifier_env repr.rank in
              Pool.add the_vars_pool uvar;
              false
            end
          )
          pool_vars
        in
        begin match pscheme with
          | None ->
              assert (List.length young_vars = 0)
          | Some pscheme ->
              Error.debug
                "[SPscheme] Putting %d vars in the pattern scheme\n"
                (List.length young_vars);
              (* Maintain the invariant that these variables are sorted in the
               * global order. *)
              let young_vars = sort_global young_vars in
              Error.debug "%a" debug_inpool (None, young_vars, sub_env);
              pscheme.p_young_vars <- young_vars
        end;

        (* The schemes have already been allocated when generating a CamlX term,
         * However, the [var_map] is a mapping from identifiers to [(uvar,
         * scheme)] where uvar represents the pre-allocated variable and scheme
         * the pre-allocated scheme for that variable. They have been unified at
         * the beginning of [solve_branch]. *)
        IdentMap.fold
          (fun ident (`Var _uvar, scheme) new_map ->
            Error.debug "%a" debug_scheme (scheme, ident);
            IdentMap.add ident scheme new_map)
          var_map new_map

      in
      let new_map =
        List.fold_left solve_branch (get_scheme_of_ident unifier_env) schemes
      in
      let new_env = set_scheme_of_ident unifier_env new_map in
      analyze new_env c
  in
  let initial_env = fresh_env () in
  try
    analyze initial_env konstraint;
    raise (Error MalformedConstraint)
  with
    | Done knowledge ->
        let kv = IdentMap.to_list knowledge in
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
        `Ok
    | Error e ->
        `Error e
