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
    | `Construct (_, ts, _, e) ->
        1 + List.fold_left (fun acc e -> acc + count_expr e) 0 e
        + List.fold_left (fun acc t -> acc + count_type t) 0 ts
    | `IfThenElse (i, t, e) ->
        1 + count_expr i + count_expr t + (match e with
        | Some e -> count_expr e
        | None -> 0)
    | `Sequence (e1, e2) ->
        1 + count_expr e1 + count_expr e2
    | `AssertFalse _
    | `Magic _
    | `Const _ ->
        1

  and count_pat = function
    | `Var _ ->
        1
    | `Tuple p ->
        1 + List.fold_left (fun acc p -> acc + count_pat p) 0 p
    | `Or (p1, p2) ->
        1 + count_pat p1 + count_pat p2
    | `Construct (_, p) ->
        1 + List.fold_left (fun acc (p, t) -> acc + count_pat p + count_type t) 0 p
    | `Const _
    | `Any ->
        1
    | `Alias (p, _) ->
        1 + count_pat p

  and count_type = function
    | `Var _ ->
        1
    | `Cons (_, ts) ->
        1 + (List.fold_left (fun acc t -> acc + count_type t) 0 ts)
    | `Forall t ->
        1 + count_type t

  and count_struct = function
    | `Let (_, pe) ->
        1 + List.fold_left
          (fun acc (p, { f_type_term; _ }, e) ->
            acc + count_type f_type_term + count_pat p + count_expr e)
          0 pe
    | _ ->
        failwith "TODO: count top-level type declarations"
  in
  List.fold_left (fun acc x -> acc + count_struct x) 0 e

open Parsetree

module AtomMap = Jmap.Make(Atom)

let count_core_nodes (e: Core.structure) =
  let rec count_expr: Core.expression -> int = function
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
          List.fold_left (fun acc (_k, t, e) -> count_type t + count_expr e + acc)
          0 map
        in
        1 + v + count_expr e2
    | `App (e, es) ->
        1 + count_expr e + (List.fold_left (fun acc e -> acc + count_expr e) 0 es)

    | `Construct (_, es)
    | `Tuple es ->
        1 + (List.fold_left (fun acc e -> acc + count_expr e) 0 es)
    | `Instance _
    | `Const _
    | `Magic _ ->
        1

    | `Sequence (e1, e2) ->
        1 + count_expr e1 + count_expr e2

    | `IfThenElse (e1, e2, e3) ->
        1 + count_expr e1 + count_expr e2 + count_expr e3

    | `Coerce (e, c) ->
        1 + count_expr e + count_coerc c

  and count_pat: Core.pattern -> int = function
    | `Var _ ->
        1
    | `Construct (_, p) ->
        1 + List.fold_left (fun acc p -> acc + count_pat p) 0 p
    | `Tuple p ->
        1 + List.fold_left (fun acc p -> acc + count_pat p) 0 p
    | `Alias (p1, p2) ->
        let p2 = (p2 :> Core.pattern) in
        1 + count_pat p1 + count_pat p2
    | `Or (p1, p2) ->
        1 + count_pat p1 + count_pat p2
    | `Const _
    | `Any ->
        1
    | `Coerce (p, c) ->
        1 + count_pat p + count_coerc c

  and count_types: DeBruijn.type_term list -> int = fun ts ->
    List.fold_left (fun acc t -> acc + count_type t) 0 ts

  and count_type: DeBruijn.type_term -> int = function
    | `Var _ ->
        1
    | `Cons (_, ts) ->
        1 + count_types ts
    | `Forall t ->
        1 + count_type t
    | `Named (_, ts) ->
        1 + count_types ts
    | `Sum ts
    | `Prod ts ->
        1 + (List.fold_left (fun acc (_, ts) -> acc + count_types ts) 0 ts)

  and count_coerc: Core.coercion -> int = function
    | `Id | `ForallIntro | `DistribTuple | `DistribVariant ->
        1
    | `Compose (c1, c2) ->
        1 + count_coerc c1 + count_coerc c2
    | `ForallCovar c ->
        1 + count_coerc c
    | `ForallElim t ->
        1 + count_type t
    | `CovarVariant (_, c)
    | `CovarTuple (_, c) ->
        1 + count_coerc c
    | `Unfold (_, ts)
    | `Fold (_, ts) ->
        1 + count_types ts

  and count_struct = function
    | `Let (pat, expr) ->
        count_pat pat + count_expr expr + 1
    | `LetRec l ->
       1 + List.fold_left
        (fun acc (_v, t, e) -> count_type t + count_expr e + acc) 0 l
    | _ ->
        failwith "TODO: count top-level type declarations"
  in

  List.fold_left (fun acc x -> acc + count_struct x) 0 e

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
