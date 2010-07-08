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
}

let find atom { type_of_atom } =
  AtomMap.find atom type_of_atom

let add atom typ { type_of_atom } =
  { type_of_atom = AtomMap.add atom typ type_of_atom }

let fail msg =
  failwith msg

let rec infer_expr: env -> Core.expression -> DeBruijn.type_term =
  fun env expr ->
    match expr with
    | `TyAbs expr ->
        let new_env =
          { type_of_atom = AtomMap.map DeBruijn.lift env.type_of_atom }
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
          let bound_identifiers = infer_pat pat t1 in
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
              if t <> t1 then
                fail "App(1)";
              t2
          | _ ->
              fail "App(2)"
        in
        List.fold_left apply t0 ti

    | `Instance (`Var x) ->
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

    (* | `Coerce (e, c) ->
        apply_coerc (infer_expr env e) c *)

and infer_letrec: 'a. env -> _ -> (env -> 'a) -> 'a =
  fun env pat_type_exprs k ->
    (* First we add into the environment all the identifiers *)
    let env = List.fold_left
      (fun acc (p, t, _e) ->
        let `Var a = p in
        add a t acc)
      env pat_type_exprs
    in
    (* What this function does is: go through all Λ and ▸ to find the
     * expression beneath, type-checks it, and returns the inferred type
     * with the Λ and ▸ taken into account (that's for e2), and the type
     * without them taken into account, that's for checking against the
     * annotated type in the AST. That way, we erase all previous type
     * definitions and we possibly apply coercions on-the-fly yeah. *)
    let env = List.fold_left
      (fun env_acc (`Var a, announced_type, e) ->
        let inferred_type = infer_expr env e in
        if inferred_type <> announced_type then
          fail "Letrec";
        add a inferred_type env_acc)
      env
      pat_type_exprs
    in
    k env

and infer_pat: Core.pattern -> DeBruijn.type_term -> (Atom.t * DeBruijn.type_term) list =
  fun pat t ->
    match pat with
    | `Coerce (pat, coerc) ->
        let t' = apply_coerc t coerc in
        infer_pat pat t'

    | `Any ->
        []

    | `Const c ->
        let t' = infer_const c in
        if t <> t' then
          fail "Const";
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
        match t with
        | `Cons (head_symbol, typs)
        when head_symbol = Algebra.TypeCons.head_symbol_tuple (List.length typs) ->
            let bound = List.map2 infer_pat patterns typs in
            (* TODO: assert that identifiers are all distinct (enforced in
               oCamlConstraintGenerator). *)
            let bound = List.flatten bound in
            bound
        | _ ->
            fail "Tuple"

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

and apply_coerc: DeBruijn.type_term -> Core.coercion -> DeBruijn.type_term =
  fun typ coerc ->
    match coerc with
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
        let bound_identifiers = infer_pat pat t in
        let env =
          List.fold_left (fun env (atom, t) -> add atom t env) env bound_identifiers
        in
        env

    | `Type _ ->
        failwith "TODO: implement type decls type-checking"
  in
  fun env structure ->
    List.fold_left infer_str env structure


let check str =
  let env = { type_of_atom = AtomMap.empty } in
  let env = infer_structure env str in
  ignore env
