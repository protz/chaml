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

open Algebra

type ('key, 'var) inspected_var = [
  | `Key of 'key
  | `Cons of type_cons * 'var list
]

let string_of_type:
  'var -> ('var -> ('key, 'var) inspected_var) -> string =
  fun uvar inspect_var ->
    let c = ref 0 in
    let fresh_greek_var =
      if Opts.get_opt "caml-types" then
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
    let rec print_type paren uvar =
      match inspect_var uvar with
        | `Key key ->
            begin match Jhashtbl.find_opt greek_of_repr key with
              | None -> 
                  let letter = fresh_greek_var () in
                  Hashtbl.add greek_of_repr key letter;
                  letter
              | Some letter ->
                  letter
            end
        | `Cons (cons_name, cons_args) ->
            begin match cons_name with
              | { cons_name = "->"; _ } ->
                  let op =
                    if Opts.get_opt "caml-types" then "->" else "→"
                  in
                  let t1 = print_type true (List.nth cons_args 0) in
                  let t2 = print_type false (List.nth cons_args 1) in
                  if paren then
                    Printf.sprintf "(%s %s %s)" t1 op t2
                  else
                    Printf.sprintf "%s %s %s" t1 op t2
              | { cons_name = "*"; _ } ->
                  let types = List.map (print_type true) cons_args in
                  Printf.sprintf "(%s)" (String.concat " * " types)
              | { cons_name; _ } ->
                  let types = List.map (print_type true) cons_args in
                  let args = String.concat ", " types in
                  if List.length types > 0 then
                    Printf.sprintf "(%s (%s))" cons_name args
                  else
                    Printf.sprintf "%s" cons_name
            end
    in
    print_type false uvar

let string_of_term: 'var generic_term -> string =
  let inspect_var: 'var generic_term -> ('var, 'var generic_term) inspected_var =
    function
      | `Var v -> `Key v
      | `Cons (cons_name, cons_args) -> `Cons (cons_name, cons_args)
  in
  fun type_term -> string_of_type type_term inspect_var
