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

module AtomMap = Map.Make(Atom)

type env = {
  type_of_atom: AtomMap.t;
}

let find atom { type_of_atom } =
  AtomMap.find atom type_of_atom

let add atom typ { type_of_atom } =
  { AtomMap.add atom typ type_of_atom }

type typ = [
  | `Cons of Algebra.TypeCons.type_cons * typ list
  | `Forall of typ
  | `Var of DeBruijn.t
]

let fail msg =
  failwith msg

let to_typ type_term =
  (type_term: DeBruijn.type_term :> typ)

let rec infer env expr: env -> Core.expression -> Algebra.type_term =
  match expr with
  | `TyAbs expr ->
      let typ = infer env expr in
      `Forall typ

  | `TyApp expr t2 ->
      let t1 = infer env expr in
      begin match t1 with
        | `Forall t1 ->
            DeBruijn.subst t2 0 t1  
        | _ ->
            fail "TyApp"
      end

  | `Fun ((`Var x), t, expr) ->
      let t = to_typ t in
      let env = add x t env in
      type_cons_arrow t (infer env expr)

  | `Match (e1, pat_exprs) ->
      let t1 = infer env e1 in
      let infer_branch (pat, expr) =
        let bound_identifiers = infer_pat pat t1 in
        let env =
          List.fold_left (fun env (atom, t) -> add atom t env) env bound_identifiers
        in
        infer env expr
      in
      let ti = List.map infer_branch pat_exprs in
      let t0 = List.hd ti in
      if (List.exists ((<>) t0) ti) then
        fail "Match";
      t0

  | `Let (`Var x, e1, e2) ->
      let t1 = infer env e1 in
      let env = add x t1 env in
      let t2 = infer env e2 in
      t2

  | `App (expr, exprs) ->
      let t0 = infer env expr in
      let ti = List.map (infer env) exprs in
      let apply t0 t =
        match t0 with
        | `Cons (TypeCons.type_cons_arrow, [t1; t2]) ->
            if t <> t1 then
              fail "App(1)";
            t2
        | _ ->
            fail "App(2)"
      in
      List.fold_left apply t0 ti

  | `Instance x ->
      let t = find x env in
      t

  | `Tuple exprs ->
      type_cons_tuple (List.map (infer env) exprs)

  | `Const const ->
      infer_const const

and infer_pat: pat -> typ -> (atom * typ) list =
  fun pat t ->
    match pat with
    | `Coerce (pat, coerc) ->
        let t' = apply_coerc t coerc in
        infer_pat pat t'

    | `Any ->
        []

    | `Var atom ->
        [atom, t]

    | `Or (p1, p2) ->
        let bound1 = infer_pat p1 t in
        let bound2 = infer_pat p2 t in
        assert (List.length bound1 <> List.length bound2);
        let tbl = Hashtbl.create 2 in
        List.iter (fun (atom, typ) -> Hashtbl.add atom typ) bound1;
        List.iter (fun (atom, typ) -> assert Hashtbl.find atom = typ) bound2;
        bound1

    | `Tuple patterns ->
        match t with
        | `Cons (TypeCons.type_cons_tuple typs) ->
            let bound = List.map2 infer_pat patterns typs in
            (* Do a assert here *)
            let bound = List.flatten bound in
            bound
        | _ ->
            fail "Tuple"

and infer_const: Core.const -> typ = function
  | `Char ->
      type_cons_char
  | `Int ->
      type_cons_int
  | `Float ->
      type_cons_float
  | `String ->
      type_cons_string
  | `Unit ->
      type_cons_unit

and apply_coerc: typ -> Core.coercion -> typ =
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
            DeBruijn.subst t2 0 t1
        | _ ->
            fail "Bad coercion"
        end

    | `CovarTuple (i, coerc) ->
        begin match typ with
        | `Cons (TypeCons.type_cons_tuple, types) ->
            let types =
              Jlist.mapi
                (fun i' t -> if i = i' then apply_coerc t coerc else t)
                types
            in
            `Cons (TypeCons.type_cons_tuple, types)
        | _ ->
            fail "Bad coercion"
        end

    | `DistribTuple ->
        begin match typ with
        | `Forall (`Cons (TypeCons.type_cons_tuple, types)) ->
            `Cons (TypeCons.type_cons_tuple, List.map (fun t -> `Forall t) types)
        | _ ->
            fail "Bad coercion"
        end
