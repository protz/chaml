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

exception Error of string

open Algebra.Identifiers
open Algebra.TypeCons
open Algebra.Core
open TypePrinter

(* We first need to define those types. These are needed for the Basesolver. *)

type descriptor = {
  mutable term: unifier_term option;
  name: string;
  mutable rank: int;
  mutable ready: bool;
}

and unifier_var = descriptor UnionFind.point
and unifier_term = [
  `Cons of type_cons * unifier_var list
]
and unifier_scheme = {
  mutable scheme_var: unifier_var;
}

type unifier_instance = unifier_var list ref

(* Now we can define cleanly the {!Algebra.SOLVER}. *)

module BaseSolver = struct
  type var = unifier_var
  type scheme = unifier_scheme
  type instance = unifier_instance

  let new_var name =
    UnionFind.fresh { name; rank = -1; term = None; ready = false }

  let new_scheme () = {
    scheme_var =
      UnionFind.fresh
        { name = fresh_name ~prefix:"scheme" (); rank = -1; term = None; ready = false }
  }

  let new_instance () = ref []

  let string_of_var uvar = (UnionFind.find uvar).name
end

module Uhashtbl = Jhashtbl.Make(struct
    type t = descriptor
    let equal = (==)
    let hash d = Hashtbl.hash d.name
  end)

(* A pool contains all the variables with a given rank. *)

module Pool = struct
  type t = {
    rank: int;
    mutable members: unifier_var list;
  }

  let add t v =
    t.members <- v :: t.members

  let add_list t l =
    t.members <- l @ t.members

  let base_pool = {
    rank = 0;
    members = [];
  }

  let next t = {
    rank = t.rank + 1;
    members = [];
  }
end

(* This is used by the solver to pass information down the recursive calls.
 * - We can use a Hashtbl because all type variables are distinct (although
 * strictly speaking we should use a map for scopes).
 * - The map is required because we need different ident maps for each branch of
 * multiple simultaneous let bindings. Moreover, it is important in a `Conj
 * constraint not pollute one branch's scope with the other one's.*)
type unifier_env = {
  current_pool: int;
  pools: Pool.t InfiniteArray.t;
  scheme_of_ident: unifier_scheme IdentMap.t;
}

(* This occurs quite frequently *)
let get_pool env i =
  assert (i <= env.current_pool && i >= 0);
  InfiniteArray.get env.pools i

let current_pool env = get_pool env env.current_pool
let current_rank env = (current_pool env).Pool.rank
let scheme_of_ident unifier_env = unifier_env.scheme_of_ident
let set_scheme_of_ident unifier_env scheme_of_ident = { unifier_env with scheme_of_ident }
let fresh_env () = {
    current_pool = 0;
    pools = InfiniteArray.make Pool.base_pool;
    scheme_of_ident = IdentMap.empty;
  }

(* This creates a new environment with a fresh pool inside that has
 * current_rank+1 *)
let step_env env =
  let new_rank = current_rank env + 1 in
  let new_pool = { Pool.rank = new_rank; Pool.members = [] } in
  let new_pool_index = env.current_pool + 1 in
  InfiniteArray.set env.pools new_pool_index new_pool;
  { env with current_pool = new_pool_index; }

(* Transforms the unification graph into a non-cyclic structure where cycles
 * have been replaced by `Alias, suitable for printing. The ?debug optional
 * parameter is used when printing a unification variable whose internal name we
 * want to display (to track unification progress). Do not use it if you want to
 * see a "real" type. *)
let inspect_scheme: ?debug:unit -> unifier_var -> unifier_var list * unifier_var inspected_var =
  fun ?debug uvar ->
    let seen = Uhashtbl.create 16 in
    let young_vars = Uhashtbl.create 16 in
    let rec inspect_uvar: unifier_var -> unifier_var inspected_var =
    fun uvar ->
      let repr = UnionFind.find uvar in
      begin match Uhashtbl.find_opt seen repr with
        | Some None ->
            let key = uvar in
            Uhashtbl.replace seen repr (Some key);
            Uhashtbl.replace young_vars repr uvar;
            `Var key
        | Some (Some key) ->
            `Var key
        | None ->
            if (not (Option.unit_bool debug)) then
              assert (repr.rank = (-1));
            Uhashtbl.add seen repr None;
            let type_term =
              match repr.term with
                | Some (`Cons (type_cons, cons_args)) ->
                    `Cons (type_cons, List.map inspect_uvar cons_args)
                | None ->
                    Uhashtbl.replace young_vars repr uvar;
                    `Var uvar
            in
            let r = begin match Uhashtbl.find_opt seen repr with
              | Some (Some key) ->
                  `Alias (type_term, `Var key)
              | Some None ->
                  Uhashtbl.remove seen repr;
                  if Option.unit_bool debug && repr.term <> None then
                    `Alias (type_term, `Var uvar)
                  else
                    type_term
              | None ->
                  assert false
            end
            in
            r
      end
    in
    Uhashtbl.map_list young_vars (fun k v -> v), inspect_uvar uvar

let debug_var_printer = `Custom (fun uvar -> (UnionFind.find uvar).name)
let regular_var_printer = `Auto (fun uvar -> (UnionFind.find uvar).name)

(* This is mainly for debugging *)
let rec uvar_name: Buffer.t -> unifier_var -> unit =
  fun buf uvar -> match UnionFind.find uvar with
    | { name = s; term = None; _ } ->
        Printf.bprintf buf "%s" s
    | { name = s; term = Some cons; _ } ->
        Buffer.add_string buf
          (string_of_type ~string_of_key:debug_var_printer (snd (inspect_scheme ~debug:() uvar)))

(* For error messages *)
let string_of_uvar ?debug ?young_vars:opt_young_vars ?caml_types uvar =
  let string_of_key = if Option.unit_bool debug then debug_var_printer else regular_var_printer in
  let young_vars, inspected_var = inspect_scheme ?debug uvar in
  let young_vars = Option.map (fun () -> young_vars) opt_young_vars in
  string_of_type ?string_of_key ?caml_types ?young_vars inspected_var

(* For error messages. Same distinction, see typePrinter.mli *)
let string_of_uvars ?caml_types uvars =
  let _young_vars, inspected_vars = List.split (List.map inspect_scheme uvars) in
  string_of_types ~string_of_key:regular_var_printer ?caml_types inspected_vars

(* For printing type schemes *)
let string_of_scheme ?debug ?caml_types ident scheme =
  let { scheme_var; } = scheme in
  Printf.sprintf "val %s: %s" ident (string_of_uvar ?debug ~young_vars:() ?caml_types scheme_var)

(* Create a fresh variable and add it to the current pool *)
let fresh_unifier_var ?term ?prefix ?name unifier_env =
  let current_pool = current_pool unifier_env in
  let rank = current_rank unifier_env in
  let name =
    match name with
      | None ->
          let prefix = Option.map_none "uvar" prefix in
          fresh_name ~prefix ()
      | Some name ->
          name
  in
  let uvar = UnionFind.fresh { term; name; rank; ready = true } in
  Pool.add current_pool uvar;
  uvar

(* Create a fresh copy of a scheme for instanciation *)
let fresh_copy unifier_env { scheme_var = scheme_uvar } =
  let mapping = Uhashtbl.create 16 in
  let rec fresh_copy uvar =
    let repr = UnionFind.find uvar in
    match Uhashtbl.find_opt mapping repr with
      | Some uvar' ->
           uvar'
      | None ->
          begin match repr.term with
            | None ->
                if repr.rank = (-1) then begin
                  let new_uvar = fresh_unifier_var unifier_env in
                  Uhashtbl.add mapping repr new_uvar;
                  new_uvar
                end else begin
                  uvar
                end
            | Some (`Cons (cons_name, cons_args)) ->
                if repr.rank = (-1) then begin
                  let new_uvar = fresh_unifier_var unifier_env in
                  let new_repr = UnionFind.find new_uvar in
                  Uhashtbl.add mapping repr new_uvar;
                  let cons_args' = List.map fresh_copy cons_args in
                  let term = Some (`Cons (cons_name, cons_args')) in
                  new_repr.term <- term;
                  new_uvar
                end else begin
                  uvar
                end
          end
  in
  let young_vars = Uhashtbl.map_list mapping (fun k v -> if k.term = None then Some v else None) in
  let young_vars = Jlist.filter_some young_vars in
  let print_pairs buf () =
    let pairs = Uhashtbl.map_list
      mapping
      (fun k v -> let n = k.name in Jstring.bsprintf "%s: %a" n uvar_name v)
    in
    Buffer.add_string buf (String.concat ", " pairs)
  in
  Error.debug "[UCopy] Mapping: %a\n" print_pairs ();
  { scheme_var = fresh_copy scheme_uvar }, young_vars

(* This actually sets up the rank properly and adds the variable in the current
 * pool if this hasn't been done already. Extremely useful when the solver
 * encounters variables that have been allocated by the constraint generator and
 * that are not ready yet. *)
let ensure_ready unifier_env uvar =
  let repr = UnionFind.find uvar in
  if not repr.ready then begin
    repr.rank <- current_rank unifier_env;
    let open Pool in
    (current_pool unifier_env).members <- (uvar :: (current_pool unifier_env).members);
    repr.ready <- true;
  end

(* What we have is bare unifier vars that don't have a proper rank, etc. So if
 * we haven't seen them yet, we set their rank properly, and we add them to the
 * environment's hash table.
 *
 * BEWARE BEWARE: the following nasty sequence of events can happen:
 * - uvar_of_term uvar
 * - unify uvar with something else
 * - uvar's hash changes
 * - uvar_of_term uvar
 *
 * We cannot use the full variable as the key for the Hashtbl. We cannot use its
 * repr either. So we must use the name (what a pity!). We might have a
 * uniquely-generated (Oo.id (object end)) later on but for now on that'll be ok
 * (have a look at fresh_name in Algebra to convince yourself the names are
 * globally unique). *)
let rec uvar_of_term: unifier_env -> unifier_var type_term -> unifier_var =
  let known_terms = Hashtbl.create 64 in
  fun unifier_env type_term ->
    let rec uvar_of_term tterm =
      match tterm with
        | `Var uvar ->
            ensure_ready unifier_env uvar;
            uvar
        | `Cons (cons, args) ->
            let term = `Cons (cons, List.map uvar_of_term args) in
            let uvar = fresh_unifier_var ~term unifier_env in
            Hashtbl.add known_terms tterm uvar;
            uvar
    in
    uvar_of_term type_term

let debug_unify =
  fun v1 v2 ->
    Error.debug "[UUnify] Unifying %a(%d) with %a(%d)\n"
      uvar_name v1 (UnionFind.find v1).rank uvar_name v2 (UnionFind.find v2).rank

(* The exceptions that might be thrown in the process. *)
type error =
  | CannotUnify of unifier_var * unifier_var
  | ArityMismatch of unifier_var * int * unifier_var * int
exception Error of error
let raise_error x = raise (Error x)

(* Update all the mutable data structures to take into account the new equation.
* The descriptor that is kept by UnionFind is that of the *second* argument. *)
let unify unifier_env v1 v2 =
  let rec unify: unifier_env -> unifier_var -> unifier_var -> unit =
    fun unifier_env v1 v2 ->
    if not (UnionFind.equivalent v1 v2) then
      (* Keeps the second argument's descriptor and updates the rank *)
      let repr1, repr2 = UnionFind.find v1, UnionFind.find v2 in
      let merge v1 v2 =
        let r = min repr1.rank repr2.rank in
        UnionFind.union v1 v2;
        repr2.rank <- r;
        repr1.rank <- r;
      in
      debug_unify v2 v1;
      assert (repr1.rank >= 0 && repr2.rank >= 0);
      match repr1, repr2 with
        | { term = Some t1; _ }, { term = Some t2; _ } ->
            let `Cons (c1, args1) = t1 and `Cons (c2, args2) = t2 in
            if not (c1 == c2) then
              raise_error (CannotUnify (v1, v2));
            let l1, l2 = List.length args1, List.length args2 in
            if not (l1 = l2) then
              raise_error (ArityMismatch (v1, l1, v2, l2));
            List.iter2 (fun arg1 arg2 -> unify unifier_env arg1 arg2) args1 args2;
            merge v1 v2;
        | { term = Some _; _ }, { term = None; _ } ->
            merge v2 v1;
        | { term = None; _ }, { term = Some _; _ } ->
            merge v1 v2;
        | { term = None; _ }, { term = None; _ } ->
            merge v1 v2
  in
  try
    unify unifier_env v1 v2;
    `Ok
  with
    | Error e -> `Error e

let string_of_error = function
    | CannotUnify (v1, v2) ->
        let s1, s2 = match string_of_uvars [v1; v2] with
            [s1; s2] -> s1, s2
          | _ -> assert false
        in
        Printf.sprintf "Cannot unify %s with %s\n" s1 s2
    | ArityMismatch (v1, l1, v2, l2) ->
        Printf.sprintf
          "Type constructor %s with %d arguments cannot be unified with %s which has %d arguments\n"
          (string_of_uvar v1) l1 (string_of_uvar v2) l2
