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

open Algebra.Core
open Algebra.TypeCons

type 'var inspected_var = [
    'var type_var
  | `Cons of head_symbol * 'var inspected_var list
  | `Alias of 'var inspected_var * 'var type_var
  | `Forall of 'var inspected_var
  | `Prod of (string * 'var inspected_var list) list
  | `Sum of (string * 'var inspected_var list) list
  | `Named of string * 'var inspected_var list
]

type ('var, 'uniq) var_printer = [
    `Auto of 'var -> 'uniq
  | `Custom of 'var -> string
]

let prec =
  let tbl = Hashtbl.create 4 in
  Hashtbl.add tbl "->" 1;
  Hashtbl.add tbl "*" 2;
  List.iter
    (fun x -> Hashtbl.add tbl x 3)
    ["int"; "char"; "float"; "string"; "unit"];
  fun op ->
    match Jhashtbl.find_opt tbl op with
      | Some p -> p
      | None -> 0

let string_of_types
    ~(string_of_key: ('var, 'uniq) var_printer)
    ?caml_types:(opt_caml_types=false)
    ?(young_vars: unit option)
    uvars =
  let c = ref 0 in
  let fresh_greek_var =
    if opt_caml_types then
      let a = (int_of_char 'a') - 1 in
      fun () ->
        c := !c + 1;
        Printf.sprintf "'%c" (char_of_int (!c + a))
    else
      let alpha = 0xB0 in
      fun () ->
        c := !c + 1;
        if (!c > 24) then Error.fatal_error "Out of Greek letters!\n";
        String.concat "" [
          "\xCE";
          String.make 1 (char_of_int (alpha + !c));
        ]
  in
  let greek_of_repr = Hashtbl.create 24 in
  let string_of_key = match string_of_key with
    | `Auto uniq ->
        (fun key ->
          let uniq_key = uniq key in
          begin match Jhashtbl.find_opt greek_of_repr uniq_key with
            | None ->
                let letter = fresh_greek_var () in
                Hashtbl.add greek_of_repr uniq_key letter;
                letter
            | Some letter ->
                letter
          end)
    | `Custom f ->
        f
  in
  let rec print_type paren uvar =
    match uvar with
      | `Forall _ as t ->
          let rec wrap acc = function
            | `Forall t ->
                wrap ("∀"::acc) t
            | t ->
                let pre = if List.length acc > 0 then ". " else "" in
                let s = print_type paren t in
                (String.concat "" (acc @ [pre; s]))
          in 
          wrap [] t

      | `Alias (uvar, key) ->
          Printf.sprintf "(%s as %s)"
            (print_type false uvar)
            (print_type false (key :> 'var inspected_var))

      | `Var key ->
          string_of_key key

      | `Cons (head_symbol, cons_args) ->
          if head_symbol == Algebra.TypeCons.head_symbol_arrow then
            let op =
              if opt_caml_types then "->" else "→"
            in
            let arg1 = List.nth cons_args 0 in
            let arg2 = List.nth cons_args 1 in
            let p1 = match arg1 with
              | `Cons ({ cons_name; _ }, _) ->
                  prec cons_name <= prec "->"
              | _ -> true
            in
            let t1 = print_type p1 arg1 in
            let t2 = print_type false arg2 in
            if paren then
              Printf.sprintf "(%s %s %s)" t1 op t2
            else
                  Printf.sprintf "%s %s %s" t1 op t2
          else if head_symbol == Algebra.TypeCons.head_symbol_tuple (List.length cons_args) then
            let types = List.map (print_type true) cons_args in
            let types = (String.concat " * " types) in
            if paren then
              Printf.sprintf "(%s)" types
            else
              types
          else
            let types = List.map (print_type true) cons_args in
            let args = String.concat ", " types in
            if List.length types > 1 then
              Printf.sprintf "((%s) %s)" args head_symbol.cons_name
            else if List.length types = 1 then
              Printf.sprintf "(%s %s)" args head_symbol.cons_name
            else
              Printf.sprintf "%s" head_symbol.cons_name

      | `Sum items ->
          let items = List.map (fun (l, ts) ->
            if List.length ts > 0 then
              let ts = List.map (print_type paren) ts in
              let ts = String.concat " * " ts in
              Printf.sprintf "%s of %s" l ts
            else
              l
            ) items
          in
          let items = String.concat " + " items in
          Printf.sprintf "∑ %s" items

      | `Prod items ->
          let items = List.map (fun (l, ts) ->
            if List.length ts > 0 then
              let ts = List.map (print_type paren) ts in
              let ts = String.concat " * " ts in
              Printf.sprintf "%s of %s" l ts
            else
              l
            ) items
          in
          let items = String.concat " × " items in
          Printf.sprintf "∏ %s" items

      | `Named (t, args) ->
          let args = List.map (print_type paren) args in
          let args = String.concat ", " args in
          Printf.sprintf "(%s) %s" args t
  in
  let print_with_scheme uvar =
    let typ = print_type false uvar in
    let vars = Jhashtbl.map_list greek_of_repr (fun _k v -> v) in
    if List.length vars > 0 then
      let vars = String.concat " " vars in
      Printf.sprintf "∀ %s. %s" vars typ
    else
      Printf.sprintf "%s" typ
  in
  match young_vars with
    | Some () when opt_caml_types = false ->
        List.map print_with_scheme uvars
    | _ ->
        List.map (print_type false) uvars

let string_of_type ~string_of_key ?caml_types ?young_vars uvar =
  List.hd (string_of_types ~string_of_key ?caml_types ?young_vars [uvar])

let string_of_term ~string_of_key type_term =
    string_of_type ~string_of_key (type_term: 'var type_term :> 'var inspected_var)
