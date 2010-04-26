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

exception Error of error
let raise_error x = raise (Error x)

let string_of_error = function
  | UnifyError e ->
      Unify.string_of_error e
  | UnboundIdentifier i ->
      Printf.sprintf "Unbound identifier %s\n" (string_of_ident i)

let unify_or_raise unifier_env uvar1 uvar2 =
  match (unify unifier_env uvar1 uvar2) with
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
  fun ~caml_types:opt_caml_types
    ~print_types:opt_print_types
    konstraint ->

  let rec analyze: unifier_env -> type_constraint -> unifier_env =
    fun unifier_env type_constraint ->
    match type_constraint with
      | `True ->
          Error.debug "[STrue] Returning from True\n";
          unifier_env
      | `Equals (`Var uvar1, t2) ->
          ensure_ready unifier_env uvar1;
          let uvar2 = uvar_of_term unifier_env t2 in
          Error.debug "[SEquals] %a = %a\n" uvar_name uvar1 uvar_name uvar2;
          unify_or_raise unifier_env uvar1 uvar2;
          unifier_env
      | `Instance (ident, `Var uvar, solver_instance) ->
          (* For instance: ident = f (with let f x = x), and t = int -> int
           * scheme is basically what came out of solving the left branch of the
           * let. young_vars is all the young variables that are possibly
           * quantified inside that scheme *)
          ensure_ready unifier_env uvar;
          let scheme =
            try
              IdentMap.find ident (scheme_of_ident unifier_env)
            with
              Not_found ->
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
          unifier_env
      | `Conj (c1, c2) ->
          (* Do *NOT* forward _unifier_env! Identifiers in c1's scope must not
           * go through c2's scope, this would be fatal. *)
          let _unifier_env = analyze unifier_env c2 in
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
  and schedule_schemes: unifier_env -> type_scheme list -> type_constraint -> unifier_env =
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
        let vars, konstraint, var_map = scheme in
        (* Make sure we register the variables that haven't been initialized yet
         * into the sub environment's pool, that's where they belong. *)
        IdentMap.iter
          (fun ident (`Var uvar, scheme) ->
             ensure_ready sub_env uvar;
             ensure_ready sub_env scheme.scheme_var;
             unify_or_raise sub_env scheme.scheme_var uvar;
          )
          var_map;

        (* --- Debug --- *)
        Error.debug "%a" (fun buf () ->
          let idents = IdentMap.keys var_map in
          let idents = List.map string_of_ident idents in
          let idents = String.concat ", " idents in
          Buffer.add_string buf (Bash.color 219 "[SLeft] Solving scheme for %s\n" idents);
        ) ();
        let debug_inpool ?prev_ranks l =
          let rank = current_rank sub_env in
          let members = match prev_ranks with
            | None ->
                List.map
                  (fun x ->
                     let repr = (UnionFind.find x) in
                       Printf.sprintf "%s(%d)" repr.name repr.rank)
                  l
            | Some ranks ->
                List.map2
                  (fun var old_rank ->
                    let repr = (UnionFind.find var) in
                    if old_rank <> repr.rank then
                      Bash.color 42 "%s(%d)" repr.name repr.rank
                    else
                      Printf.sprintf "%s(%d)" repr.name repr.rank)
                  l ranks
          in
          Error.debug "%a"
            (fun buf () -> Buffer.add_string buf (
              Bash.color 208 "[InPool] %d: %s\n" rank (String.concat ", " members)))
            ();
        in
        let debug_scheme buf (scheme, ident) =
          let scheme_str = string_of_scheme
            ~debug:()
            (string_of_ident ident)
            scheme
          in
          let str = Bash.color 185 "[SScheme] Got %s\n" scheme_str in
          Buffer.add_string buf str
        in
        (* --- End Debug --- *)

        (* Solve the constraint in the scheme. *)
        let _sub_unifier_env =
          analyze sub_env konstraint
        in
        let sub_pool = current_pool _sub_unifier_env in
        let young_vars = sub_pool.Pool.members in

        (* We want to keep "young" variables that have been introduced while
         * solving the constraint attached to that branch. We don't want to
         * quantify over variables that represent constructors, that's useless. *)
        let is_young uvar =
          let desc = UnionFind.find uvar in
          assert (desc.rank <= current_rank sub_env);
          desc.rank = current_rank sub_env
        in

        (* Filter out duplicates. This isn't necessary but still this should
         * speed things up. *)
        let young_vars =
          Jlist.remove_duplicates
            ~hash_func:(fun x -> Hashtbl.hash (UnionFind.find x))
            ~equal_func:UnionFind.equivalent
            young_vars
        in

        (* This is rank propagation. See lemma 10.6.7 in ATTAPL. This is needed. *)
        debug_inpool young_vars;
        let prev_ranks = List.map (fun x -> (UnionFind.find x).rank) young_vars in
        List.iter propagate_ranks young_vars;
        debug_inpool ~prev_ranks young_vars;

        (* We can just get rid of the old vars: they have been unified with a
         * var that's already in its own pool, with a lower rank. *)
        let young_vars, old_vars = List.partition is_young young_vars in
        debug_inpool young_vars;
        List.iter (fun x -> (UnionFind.find x).rank <- -1) young_vars;
        debug_inpool young_vars;

        (* Send back the old vars in their respective pools *)
        List.iter
          (fun var ->
            let repr = UnionFind.find var in
            let the_vars_pool = get_pool unifier_env repr.rank in
            Pool.add the_vars_pool var
          )
          old_vars;

        (* Fill in the schemes that have been pre-allocated by the constraint
         * generator. The variables are ready, that was done at the beginning. *)
        let assign_scheme: ident -> unifier_scheme = fun ident ->
          let (`Var uvar), scheme = IdentMap.find ident var_map in
          Error.debug "%a" debug_scheme (scheme, ident);
          scheme
        in
        IdentMap.fold
          (fun ident type_var -> IdentMap.add ident (assign_scheme ident))
          (var_map: (unifier_var type_var * unifier_scheme) IdentMap.t :> (unifier_var type_term * unifier_scheme) IdentMap.t)
          new_map
      in
      let new_map =
        List.fold_left solve_branch (scheme_of_ident unifier_env) schemes
      in
      let new_env = set_scheme_of_ident unifier_env new_map in
      analyze new_env c
  in
  let initial_env = fresh_env () in
  try
    let knowledge = analyze initial_env konstraint in
    (* Hashtbl.iter
      (fun k v -> Error.debug "[Rank] %s: %d\n"
                    (UnionFind.find v).name
                    (UnionFind.find v).rank)
      knowledge.uvar_of_term; *)
    let kv = IdentMap.to_list (scheme_of_ident knowledge) in
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
  with
    Error e -> `Error e
