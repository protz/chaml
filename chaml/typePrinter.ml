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

type 'var inspected_var = [
  | `Var of 'var
  | `Cons of type_cons * 'var inspected_var list
  | `Alias of 'var inspected_var * [`Var of 'var]
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

let string_of_type:
  ?string_of_key:('key -> string) -> 'key inspected_var -> string =
  fun ?string_of_key uvar ->
    let _seen = Hashtbl.create 16 in
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
    let string_of_key = match string_of_key with
      | None ->
          (fun key ->
            begin match Jhashtbl.find_opt greek_of_repr key with
              | None -> 
                  let letter = fresh_greek_var () in
                  Hashtbl.add greek_of_repr key letter;
                  letter
              | Some letter ->
                  letter
            end)
      | Some f ->
          f
    in
    let rec print_type paren uvar =
      match uvar with
        | `Alias (uvar, `Var key) ->
            Printf.sprintf "(%s as %s)" (print_type false uvar) (string_of_key key)
        | `Var key ->
            string_of_key key
        | `Cons (cons_name, cons_args) as _cons ->
            (* begin match Jhashtbl.find_opt seen cons with
              | Some None ->
                  let l = fresh_greek_var () in
                  Hashtbl.add seen cons (Some l);
                  l
              | Some (Some l) ->
                  l
              | None ->
                  Hashtbl.add seen cons None;
                  let type_string =  *)begin match cons_name with
                    | { cons_name = "->"; _ } ->
                        let op =
                          if Opts.get_opt "caml-types" then "->" else "→"
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
                  end (* in
                  begin match Jhashtbl.find_opt seen cons with
                    | Some (Some l) ->
                        Printf.sprintf "(%s as %s)" type_string l
                    | Some None ->
                        type_string
                    | None ->
                        assert false
                  end
            end *)
    in
    print_type false uvar

let string_of_term: 'var generic_term -> string =
  fun type_term ->
    string_of_type (type_term: 'var generic_term :> 'var inspected_var)