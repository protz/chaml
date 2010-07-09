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

type t = { index: int; }

type type_var = t Algebra.Core.type_var
type type_term = [
    type_var
  | `Cons of Algebra.TypeCons.head_symbol * type_term list
  | `Forall of type_term
  | `Sum of (string * type_term list) list
  | `Prod of (string * type_term list) list
  | `Named of string * type_term list
]

let index { index } = index
let zero = { index = 0 }
let of_int index = { index }

let lift_t { index } = { index = index + 1 }

let lift t =
  let rec lift i t =
    match t with
    | `Var { index = j } ->
        if j < i then `Var { index = j }
        else `Var { index = j + 1 }
    | `Forall t ->
        `Forall (lift (i+1) t)
    | `Cons (head_symbol, cons_args) ->
        `Cons (head_symbol, List.map (lift i) cons_args)
    | `Prod ts ->
        `Prod (List.map (fun (l, ts) -> (l, List.map (lift i) ts)) ts)
    | `Sum ts ->
        `Sum (List.map (fun (l, ts) -> (l, List.map (lift i) ts)) ts)
    | `Named (t, ts) ->
        `Named (t, List.map (lift i) ts)
  in
  lift 0 t

let rec subst t2 { index = i } t1 =
  let rec subst: type_term -> int -> type_term -> type_term = fun t2 i t1 ->
    match t1 with
    | `Var { index = j } ->
        if i = j then t2
        else if j < i then `Var { index = j }
        else if j > i then `Var { index = j - 1 }
        else assert false
    | `Cons (head_symbol, cons_args) ->
        `Cons (head_symbol, List.map (subst t2 i) cons_args)
    | `Forall t1 ->
        `Forall (subst (lift t2) (i + 1) t1)
    | `Prod ts ->
        `Prod (List.map (fun (l, ts) -> (l, List.map (subst t2 i) ts)) ts)
    | `Sum ts ->
        `Sum (List.map (fun (l, ts) -> (l, List.map (subst t2 i) ts)) ts)
    | `Named (t, ts) ->
        `Named (t, List.map (subst t2 i) ts)
  in
  subst t2 i t1

let string_of_t x = string_of_int x.index

let string_of_type_term scheme =
  let open TypePrinter in
  let scheme =
    (scheme: type_term :> t inspected_var)
  in
  let scheme = string_of_type
    ~string_of_key:(`Custom string_of_t)
    scheme
  in
  scheme

