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

module AtomMap = Jmap.Make(Atom)

type env = {
  type_of_atom: DeBruijn.type_term AtomMap.t;
    (** This is where we remember the type of the atoms we've seen so far. *)
  unfold_type: (int * DeBruijn.type_term) AtomMap.t;
    (** This is used to expand the definition of named types (type t = ...).
        The integer represents the arity of the type
        The type is the definition. *)
}

let find atom { type_of_atom; _ } =
  AtomMap.find atom type_of_atom

let add atom typ env =
  let type_of_atom = AtomMap.add atom typ env.type_of_atom in
  { env with type_of_atom }

let fail msg =
  failwith msg

let assert_types_equal t1 t2 =
  if t1 <> t2 then begin
    let t1 = DeBruijn.string_of_type_term t1 in
    let t2 = DeBruijn.string_of_type_term t2 in
    Error.debug "[TypeChecking#Fail] %s <> %s\n" t1 t2;
    failwith "Unrecoverable error, dying.\n"
  end

let assert_type_lists_equal l1 l2 =
  if l1 <> l2 then begin
    let t1 = String.concat "; "
      (List.map DeBruijn.string_of_type_term l1)
    in
    let t2 = String.concat "; "
      (List.map DeBruijn.string_of_type_term l2)
    in
    Error.debug "[TypeChecking#Fail] [%s] <> [%s]\n" t1 t2;
    failwith "Unrecoverable error, dying.\n"
  end


let rec infer_expr: env -> Core.expression -> DeBruijn.type_term =
  fun env expr ->
    match expr with
    | `TyAbs expr ->
        let new_env =
          let type_of_atom = AtomMap.map DeBruijn.lift env.type_of_atom in
          { env with type_of_atom }
        in
        let typ = infer_expr new_env expr in
        `Forall typ

    | `TyApp (expr, t2) ->
        let t1 = infer_expr env expr in
        Error.debug "[OTyApp] Applying type %s to type %s\n"
          (DeBruijn.string_of_type_term t2)
          (DeBruijn.string_of_type_term t1);
        begin match t1 with
          | `Forall t1 ->
              let r = DeBruijn.subst t2 DeBruijn.zero t1 in
              Error.debug "[OTyApp] This gives us %s\n" (DeBruijn.string_of_type_term r);
              r
          | _ ->
              failwith "TyApp"
        end

    | `Fun (`Var x, t, expr) ->
        let env = add x t env in
        Algebra.TypeCons.type_cons_arrow t (infer_expr env expr)

    | `Match (e1, pat_exprs) ->
        let t1 = infer_expr env e1 in
        let infer_branch (pat, expr) =
          let bound_identifiers = infer_pat env pat t1 in
          let env =
            List.fold_left (fun env (atom, t) -> add atom t env) env bound_identifiers
          in
          infer_expr env expr
        in
        let ti = List.map infer_branch pat_exprs in
        let t0 = List.hd ti in
        if (List.exists ((<>) t0) ti) then
          fail "Match";
        t0

    | `Let (`Var x, e1, e2) ->
        let t1 = infer_expr env e1 in
        Error.debug
          "[OLet] %s: %s\n" (Atom.string_of_atom x)
          (DeBruijn.string_of_type_term t1);
        let env = add x t1 env in
        let t2 = infer_expr env e2 in
        t2

    | `LetRec (pat_type_exprs, e2) ->
        infer_letrec
          env
          pat_type_exprs
          (fun env -> infer_expr env e2)

    | `App (expr, exprs) ->
        let t0 = infer_expr env expr in
        let ti = List.map (infer_expr env) exprs in
        let apply t0 t =
          Error.debug "[OApp] Function %s argument %s\n"
            (DeBruijn.string_of_type_term t0)
            (DeBruijn.string_of_type_term t);
          match t0 with
          | `Cons (head_symbol, [t1; t2])
          when head_symbol = Algebra.TypeCons.head_symbol_arrow ->
              assert_types_equal t t1;
              t2
          | _ ->
              fail "App(2)"
        in
        List.fold_left apply t0 ti

    | `Instance (`Var x) ->
        Error.debug "[OInstance] Taking an instance of %s\n"
          (Atom.string_of_atom x);
        let t = find x env in
        Error.debug "[OInstance] Scheme for %s is %s\n"
          (Atom.string_of_atom x)
          (DeBruijn.string_of_type_term t);
        t

    | `Tuple exprs ->
        Algebra.TypeCons.type_cons_tuple (List.map (infer_expr env) exprs)

    | `Const const ->
        infer_const const

    | `Magic t ->
        t

    | `Sequence _ ->
        failwith "TODO type-check sequence"

    | `Construct (label, args) ->
        let ts = List.map (infer_expr env) args in
        `Sum [label, ts]

    | `Coerce (e, c) ->
        apply_coerc env (infer_expr env e) c

and infer_letrec: 'a. env -> _ -> (env -> 'a) -> 'a =
  fun env pat_type_exprs k ->
    (* First we add into the environment all the identifiers *)
    let env = List.fold_left
      (fun acc (p, t, _e) ->
        let `Var a = p in
        Error.debug "[TC] Adding %s in the environment\n" (Atom.string_of_atom a);
        add a t acc)
      env pat_type_exprs
    in
    (* This type-checking is very simple because desugar did quite a lot of work
     * by finding all identifiers that were defined in the recursive let-rec,
     * and instanciated them with the same variables (there's no reinstanciation
     * in standard ML let-rec). *)
    let env = List.fold_left
      (fun env_acc (`Var a, announced_type, e) ->
        let inferred_type = infer_expr env e in
        assert_types_equal inferred_type announced_type;
        add a inferred_type env_acc)
      env
      pat_type_exprs
    in
    k env

and infer_pat: env -> Core.pattern -> DeBruijn.type_term -> (Atom.t * DeBruijn.type_term) list =
  fun env pat t ->
    let rec infer_pat pat t =
      match pat with
      | `Coerce (pat, coerc) ->
          let t' = apply_coerc env t coerc in
          infer_pat pat t'

      | `Any ->
          []

      | `Const c ->
          let t' = infer_const c in
          assert_types_equal t t';
          []

      | `Var atom ->
          [atom, t]

      | `Or (p1, p2) ->
          let bound1 = infer_pat p1 t in
          let bound2 = infer_pat p2 t in
          assert (List.length bound1 = List.length bound2);
          let tbl = Hashtbl.create 2 in
          List.iter (fun (atom, typ) -> Hashtbl.add tbl atom typ) bound1;
          List.iter (fun (atom, typ) -> assert (Hashtbl.find tbl atom = typ)) bound2;
          bound1

      | `Tuple patterns ->
          begin match t with
          | `Cons (head_symbol, typs)
          when head_symbol = Algebra.TypeCons.head_symbol_tuple (List.length typs) ->
              let bound = List.map2 infer_pat patterns typs in
              (* TODO: assert that identifiers are all distinct (enforced in
                 oCamlConstraintGenerator). *)
              let bound = List.flatten bound in
              bound
          | _ ->
              fail "Tuple"
          end

      | `Construct (_label, _args) ->
          failwith "TODO: infer_pat `Construct"
    in
    infer_pat pat t

and infer_const: Core.const -> DeBruijn.type_term =
  let open Algebra.TypeCons in
  function
  | `Char _ ->
      type_cons_char
  | `Int _ ->
      type_cons_int
  | `Float _ ->
      type_cons_float
  | `String _ ->
      type_cons_string

and apply_coerc: env -> DeBruijn.type_term -> Core.coercion -> DeBruijn.type_term =
  fun env typ coerc ->
    let rec apply_coerc typ =
      function
      | `Id ->
          typ
      
      | `Compose (c1, c2) ->
          let typ = apply_coerc typ c1 in
          apply_coerc typ c2

      | `ForallIntro ->
          fail "Unused"

      | `ForallCovar c ->
          begin match typ with
          | `Forall t ->
              `Forall (apply_coerc t c)
          | _ ->
              fail "Bad coercion"
          end

      | `ForallElim t2 ->
          begin match typ with
          | `Forall t1 ->
              DeBruijn.subst t2 DeBruijn.zero t1
          | _ ->
              fail "Bad coercion"
          end

      | `CovarTuple (i, coerc) ->
          begin match typ with
          | `Cons (head_symbol, types)
          when head_symbol = Algebra.TypeCons.head_symbol_tuple (List.length types) ->
              let types =
                Jlist.mapi
                  (fun i' t -> if i = i' then apply_coerc t coerc else t)
                  types
              in
              Algebra.TypeCons.type_cons_tuple types
          | _ ->
              fail "Bad coercion"
          end

      | `DistribTuple ->
          begin match typ with
          | `Forall (`Cons (head_symbol, types))
          when head_symbol = Algebra.TypeCons.head_symbol_tuple (List.length types) ->
              Algebra.TypeCons.type_cons_tuple (List.map (fun t -> `Forall t) types)
          | _ ->
              fail "Bad coercion"
          end

      | `Fold (t, args) ->
          (* We fetch the definition of type t from the environment *)
          let def_arity, def = AtomMap.find t env.unfold_type in
          if def_arity <> List.length args then
            fail "Fold coercion (0)";
          (* Fortunately, we have the invariant that args is in order *)
          let mapping = Array.of_list args in
          (* We compute what this type looks like when instanciated with args *)
          let full_type =
            let rec map = function
              | `Var v ->
                  mapping.(DeBruijn.index v)
              | `Forall t ->
                  `Forall (map t)
              | `Cons (head_symbol, cons_args) ->
                  `Cons (head_symbol, List.map map cons_args)
              | `Prod ts ->
                  `Prod (List.map (fun (l, ts) -> (l, List.map map ts)) ts)
              | `Sum ts ->
                  `Sum (List.map (fun (l, ts) -> (l, List.map map ts)) ts)
              | `Named (t, ts) ->
                  `Named (t, List.map map ts)
            in
            map def
          in
          Error.debug "%s Type is now %s\n"
            (Bash.color 203 "[TCApplyCoerc]")
            (DeBruijn.string_of_type_term full_type);
          (* We check that we can inject the anonymous sum/product into the
           * isorecursive type by checking that the labels match and that the
           * arguments match as well *)
          match full_type, typ with
          | `Sum label_args_list, `Sum [i_label, i_args] ->
              let def_label, def_args =
                List.find (fun (l, _) -> l = i_label) label_args_list
              in
              assert (def_label = i_label);
              assert_type_lists_equal def_args i_args;
              (* We're good, the coercion was right, we can fold this into type
               * "t" with args "args". *)
              `Named (t, args)
          | _ ->
              fail "Fold coercion (2)"
    in
    apply_coerc typ coerc




and infer_structure: env -> Core.structure -> env =
  let rec infer_str: env -> _ -> env =
    fun env -> function
    | `LetRec var_type_exprs ->
        infer_letrec
          env
          var_type_exprs
          (fun x -> x)

    | `Let (pat, expr) ->
        let t = infer_expr env expr in
        let bound_identifiers = infer_pat env pat t in
        let env =
          List.fold_left (fun env (atom, t) -> add atom t env) env bound_identifiers
        in
        env

    | `Type (arity, atom, t) ->
        let unfold_type = AtomMap.add atom (arity, t) env.unfold_type in
        { env with unfold_type }
  in
  fun env structure ->
    List.fold_left infer_str env structure


let check str =
  let env = { type_of_atom = AtomMap.empty; unfold_type = AtomMap.empty } in
  let env = infer_structure env str in
  ignore env
