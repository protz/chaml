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

let count_constraint_nodes c =
  let rec count = function
    | `True | `Done ->
        1
    | `Conj (c1, c2) ->
        1 + count c1 + count c2
    | `Exists (_, c) ->
        1 + count c
    | `Equals _ ->
        1
    | `Instance _ ->
        1
    | `Let (s, c) ->
        1 + (List.fold_left (fun acc (_, c, _, _) -> count c + acc) 0 s) + count c
  in
  count c

open CamlX

let count_camlx_nodes e =
  let rec count_expr = function
    | `Let (_, pe, e) ->
        1 + count_expr e +
        (List.fold_left (fun acc (p, { f_type_term; _ }, e) ->
          acc + count_type f_type_term + count_pat p + count_expr e) 0 pe)
    | `Instance (_, ts) ->
        1 + (List.fold_left (fun acc t -> acc + count_type t) 0 ts)
    | `App (e, es) ->
        1 + count_expr e + (List.fold_left (fun acc e -> acc + count_expr e) 0 es)
    | `Function (t, pe) ->
        1 + count_type t + (List.fold_left (fun acc (p, e) -> acc + count_pat p
        + count_expr e) 0 pe)
    | `Match (e, { f_type_term; _ }, pe) ->
        1 + count_expr e + (List.fold_left (fun acc (p, e) -> acc + count_pat p
        + count_expr e) 0 pe) + count_type f_type_term
    | `Tuple es ->
        1 + (List.fold_left (fun acc e -> acc + count_expr e) 0 es)
    | `Const _ ->
        1
    | `Magic _ ->
        1

  and count_pat = function
    | `Var _ ->
        1
    | `Tuple p ->
        1 + List.fold_left (fun acc p -> acc + count_pat p) 0 p
    | `Or (p1, p2) ->
        1 + count_pat p1 + count_pat p2
    | `Any ->
        1

  and count_type = function
    | `Var _ ->
        1
    | `Cons (_, ts) ->
        1 + (List.fold_left (fun acc t -> acc + count_type t) 0 ts)
    | `Forall t ->
        1 + count_type t

  in
  count_expr e

open Parsetree

module AtomMap = Jmap.Make(Atom)

let count_core_nodes e =
  let rec count_expr = function
    | `TyAbs e ->
        count_expr e + 1
    | `TyApp (e, t) ->
        count_expr e + count_type t + 1
    | `Fun (_, t, e) ->
        count_type t + count_expr e + 1
    | `Match (e, pe) ->
        count_expr e + 1 + List.fold_left
          (fun acc (p, e) -> acc + count_pat p + count_expr e) 0 pe
    | `Let (_, e1, e2) ->
        1 + count_expr e1 + count_expr e2
    | `LetRec (map, e2) ->
        let v =
          AtomMap.fold (fun k (t, e) acc -> count_type t + count_expr e + acc)
          map 0
        in
        1 + v + count_expr e2
    | `App (e, es) ->
        1 + count_expr e + (List.fold_left (fun acc e -> acc + count_expr e) 0 es)

    | `Tuple es ->
        1 + (List.fold_left (fun acc e -> acc + count_expr e) 0 es)
    | `Instance _ ->
        1
    | `Const _ ->
        1
    | `Magic _ ->
        1

  and count_pat = function
    | `Var _ ->
        1
    | `Tuple p ->
        1 + List.fold_left (fun acc p -> acc + count_pat p) 0 p
    | `Or (p1, p2) ->
        1 + count_pat p1 + count_pat p2
    | `Any ->
        1
    | `Coerce (p, c) ->
        1 + count_pat p + count_coerc c

  and count_type = function
    | `Var _ ->
        1
    | `Cons (_, ts) ->
        1 + (List.fold_left (fun acc t -> acc + count_type t) 0 ts)
    | `Forall t ->
        1 + count_type t

  and count_coerc = function
    | `Id | `ForallIntro | `DistribTuple ->
        1
    | `Compose (c1, c2) ->
        1 + count_coerc c1 + count_coerc c2
    | `ForallCovar c ->
        1 + count_coerc c
    | `ForallElim t ->
        1 + count_type t
    | `CovarTuple (_, c) ->
        1 + count_coerc c

  in
  count_expr e

let count_ocaml_nodes str =
  let rec count_pat { ppat_desc; _ } =
    match ppat_desc with
    | Ppat_any ->
        1
    | Ppat_var _ ->
        1
    | Ppat_tuple p ->
        1 + List.fold_left (fun acc p -> acc + count_pat p) 0 p
    | Ppat_or (pat1, pat2) ->
        1 + count_pat pat1 + count_pat pat2
    | _ ->
        assert false

  and count_expr { pexp_desc; _ } =
    match pexp_desc with
    | Pexp_done ->
        1
    | Pexp_ident _ ->
        1
    | Pexp_constant _ ->
        1
    | Pexp_function (_, _, pe) ->
        1 + List.fold_left (fun acc (p, e) -> count_pat p + count_expr e + acc) 0 pe
    | Pexp_apply (e1, label_expr_list) ->
        1 + count_expr e1 + List.fold_left (fun acc (_, e) -> acc + count_expr e)
        0 label_expr_list
    | Pexp_let (_, pe, e2) ->
        1 + count_expr e2 + List.fold_left (fun acc (p, e) -> count_pat p + count_expr e + acc) 0 pe
    | Pexp_match (e1, pe) ->
        1 + count_expr e1 + List.fold_left (fun acc (p, e) -> count_pat p + count_expr e + acc) 0 pe
    | Pexp_tuple (expressions) ->
        1 + List.fold_left (fun acc e -> acc + count_expr e) 0 expressions
    | _ ->
        assert false

  and count_str { pstr_desc; _ } = match pstr_desc with
    | Pstr_value (_, pe) ->
        1 + List.fold_left (fun acc (p, e) -> count_pat p + count_expr e + acc) 0 pe
    | Pstr_eval expr ->
        1 + count_expr expr
    | _ ->
        assert false
  in

  List.fold_left (fun acc str -> acc + count_str str) 0 str
