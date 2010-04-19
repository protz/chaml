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
  | `Cons of type_cons * 'var inspected_var list
  | `Alias of 'var inspected_var * 'var type_var
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
    Hashtbl.find tbl op

let string_of_types =
  fun ~(string_of_key: ('var, 'uniq) var_printer) ?caml_types:(opt_caml_types=false) ?young_vars uvars ->
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
        | `Alias (uvar, key) ->
            Printf.sprintf "(%s as %s)"
              (print_type false uvar)
              (print_type false (key :> 'var inspected_var))
        | `Var key ->
            string_of_key key
        | `Cons (cons_name, cons_args) ->
            begin match cons_name with
              | { cons_name = "->"; _ } ->
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
              | { cons_name = "*"; _ } ->
                  let types = List.map (print_type true) cons_args in
                  let types = (String.concat " * " types) in
                  if paren then
                    Printf.sprintf "(%s)" types
                  else
                    types
              | { cons_name; _ } ->
                  let types = List.map (print_type true) cons_args in
                  let args = String.concat ", " types in
                  if List.length types > 0 then
                    Printf.sprintf "(%s (%s))" cons_name args
                  else
                    Printf.sprintf "%s" cons_name
            end
    in
    let print_with_scheme young_vars uvar =
      let vars = List.map string_of_key young_vars in
      if List.length vars > 0 then
        let vars = String.concat " " vars in
        Printf.sprintf "∀ %s. %s" vars (print_type false uvar)
      else
        Printf.sprintf "%s" (print_type false uvar)
    in
    match young_vars with
      | Some young_vars when opt_caml_types = false ->
          List.map2 print_with_scheme young_vars uvars
      | _ ->
          List.map (print_type false) uvars

let string_of_type ~string_of_key ?caml_types ?young_vars uvar =
  let young_vars = Option.map (fun x -> [x]) young_vars in
  List.hd (string_of_types ~string_of_key ?caml_types ?young_vars [uvar])

let string_of_term ~string_of_key type_term =
    string_of_type ~string_of_key (type_term: 'var type_term :> 'var inspected_var)
