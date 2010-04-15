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

(* We first need to define those types. We cannot build the Algebra.Make module
 * yet as we first need to be able to defined BaseSolver *)

type descriptor = {
  mutable term: unifier_term option;
  name: string;
  mutable rank: int;
}

and unifier_var = descriptor UnionFind.point
and unifier_term = [
  `Cons of type_cons * unifier_var list
]
and unifier_scheme = unifier_var list * unifier_var

(* Since TypeCons is not a functor, we were able to bootstrap the types above.
 * Now we can create a SOLVER module (modulo one ugly hack). *)

let new_var_ref = ref (fun _ -> assert false)

module BaseSolver = struct
  type var = unifier_var
  type scheme = unifier_scheme
  type instance = unifier_var list

  let new_var name = UnionFind.fresh { name; rank = -1; term = None }
  let new_scheme () = assert false
  let new_instance () = assert false

  let string_of_var uvar = (UnionFind.find uvar).name
end

(* We're good to go! *)

module Algebra_ = Algebra.Make(BaseSolver) open Algebra_
module TypePrinter_ = TypePrinter.Make(BaseSolver) open TypePrinter_

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
  current_pool: Pool.t;
  uvar_of_tterm: (type_term, unifier_var) Hashtbl.t;
  scheme_of_ident: unifier_scheme IdentMap.t;
}

(* This occurs quite frequently *)
let current_pool env = env.current_pool
let current_rank env = env.current_pool.Pool.rank

(* This creates a new environment with a fresh pool inside that has
 * current_rank+1 *)
let step_env env =
  let new_rank = current_rank env + 1 in
  let new_pool = { Pool.base_pool with Pool.rank = new_rank } in
  { env with current_pool = new_pool }

(* Transforms the unification graph into a non-cyclic structure where cycles
 * have been replaced by `Alias, suitable for printing. The ?debug optional
 * parameter is used when printing a unification variable whose internal name we
 * want to display (to track unification progress). Do not use it if you want to
 * see a "real" type. *)
let inspect_uvar: ?debug:unit -> unifier_var -> inspected_var =
  fun ?debug uvar ->
    let seen = Hashtbl.create 16 in
    let rec inspect_uvar: unifier_var -> inspected_var =
    fun uvar ->
      let repr = UnionFind.find uvar in
      begin match Jhashtbl.find_opt seen repr with
        | Some None ->
            let key = uvar in
            Hashtbl.replace seen repr (Some key);
            `Var key
        | Some (Some key) ->
            `Var key
        | None ->
            Hashtbl.add seen repr None;
            let type_term =
              match repr.term with
                | Some (`Cons (type_cons, cons_args)) ->
                    `Cons (type_cons, List.map inspect_uvar cons_args)
                | None ->
                    `Var uvar
            in
            let r = begin match Jhashtbl.find_opt seen repr with
              | Some (Some key) ->
                  `Alias (type_term, `Var key)
              | Some None ->
                  Hashtbl.remove seen repr;
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
    inspect_uvar uvar

(* This is mainly for debugging *)
let rec uvar_name: Buffer.t -> unifier_var -> unit =
  fun buf uvar -> match UnionFind.find uvar with
    | { name = s; term = None; _ } ->
        Printf.bprintf buf "%s" s
    | { name = s; term = Some cons; _ } ->
        let string_of_key uvar = (UnionFind.find uvar).name in
        Buffer.add_string buf
          (string_of_type ~string_of_key (inspect_uvar ~debug:() uvar))

(* For error messages *)
let string_of_uvar ?string_of_key ?caml_types ?young_vars uvar =
  string_of_type ?string_of_key ?caml_types ?young_vars (inspect_uvar uvar)

(* For error messages. Same distinction, see typePrinter.mli *)
let string_of_uvars ?caml_types uvars =
  string_of_types ?caml_types (List.map inspect_uvar uvars)

(* For printing type schemes *)
let string_of_scheme ?string_of_key ?caml_types ident scheme =
  let young_vars, uvar = scheme in
  let young_vars = List.filter (fun x -> (UnionFind.find x).term = None) young_vars in
  Printf.sprintf "val %s: %s" ident (string_of_uvar ?string_of_key ~young_vars ?caml_types uvar)


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
  let uvar = UnionFind.fresh { term; name; rank; } in
  Pool.add current_pool uvar;
  uvar

(* Create a fresh copy of a scheme for instanciation *)
let fresh_copy unifier_env (young_vars, scheme_uvar) =
  let mapping = Hashtbl.create 16 in
  let call_stack = Hashtbl.create 16 in
  let base_rank = (UnionFind.find scheme_uvar).rank in
  let module L = struct exception RecType of unifier_var * unifier_var end in
  let rec fresh_copy uvar =
    let repr = UnionFind.find uvar in
    match Jhashtbl.find_opt mapping repr with
      | Some uvar' ->
          (* This clearly tells us that we've hit a recursive type: we have
           * 'a = T('a). Strictly speaking, this is not necessary. It's just
           * that if we don't do that, we're unfolding the recursive types way
           * too deep. *)
          if repr.term <> None && Hashtbl.mem call_stack uvar' then
            raise (L.RecType (uvar', uvar))
          else
            uvar'
      | None ->
          begin match repr.term with
            | None -> uvar
            | Some (`Cons (cons_name, cons_args)) ->
                if (UnionFind.find uvar).rank < base_rank then
                  uvar
                else
                  let uvar = fresh_unifier_var unifier_env in
                  try
                    Hashtbl.add mapping repr uvar;
                    Hashtbl.add call_stack uvar ();
                    let cons_args' = List.map fresh_copy cons_args in
                    Hashtbl.remove call_stack uvar;
                    let term = `Cons (cons_name, cons_args') in
                    (UnionFind.find uvar).term <- Some term;
                    uvar
                  with
                    | L.RecType (me, original) when me = uvar ->
                        Hashtbl.replace mapping repr original;
                        original
          end
  in
  List.iter
    (fun v ->
       let v' = fresh_unifier_var ~prefix:"dup" unifier_env in
       Hashtbl.add mapping (UnionFind.find v) v'
    )
    young_vars;
  let print_pairs buf () =
    let pairs = Jhashtbl.map_list
      mapping
      (fun k v -> let n = k.name in Jstring.bsprintf "%s: %a" n uvar_name v)
    in
    Buffer.add_string buf (String.concat ", " pairs)
  in
  Error.debug "[UCopy] Mapping: %a\n" print_pairs ();
  fresh_copy scheme_uvar

(* What we have is bare unifier vars that don't have a proper rank, etc. So if
 * we haven't seen them yet, we set their rank properly, and we add them to the
 * environment's hash table. *)
let rec uvar_of_tterm: unifier_env -> type_term -> unifier_var =
  fun unifier_env type_term ->
    let rec uvar_of_tterm: type_term -> unifier_var = fun tterm ->
    match Jhashtbl.find_opt unifier_env.uvar_of_tterm tterm with
      | Some uvar ->
          uvar
      | None ->
          match tterm with
            | `Var uvar ->
                (UnionFind.find uvar).rank <- current_rank unifier_env;
                let open Pool in
                unifier_env.current_pool.members <-
                  (uvar :: unifier_env.current_pool.members);
                Hashtbl.add unifier_env.uvar_of_tterm tterm uvar;
                uvar
            | `Cons (cons, args) ->
                let term = `Cons (cons, List.map uvar_of_tterm args) in
                fresh_unifier_var ~term unifier_env
    in
    uvar_of_tterm type_term

let debug_unify =
  fun v1 v2 ->
    Error.debug "[UUnify] Unifying %a with %a\n" uvar_name v1 uvar_name v2

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
      let merge v1 v2 =
        let repr1, repr2 = UnionFind.find v1, UnionFind.find v2 in
        let r = min repr1.rank repr2.rank in
        UnionFind.union v1 v2;
        repr2.rank <- r
      in
      match UnionFind.find v1, UnionFind.find v2 with
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
            debug_unify v2 v1;
            merge v2 v1;
        | { term = None; _ }, { term = Some _; _ } ->
            debug_unify v2 v1;
            merge v1 v2;
        | { term = None; _ }, { term = None; _ } ->
            debug_unify v2 v1;
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
