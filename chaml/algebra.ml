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

open Error

(* X *)
type type_var = [
  `Var of string
]

(* Generate fresh type variables on demand *)
let fresh_var =
  let c = ref (-1) in
  fun ?letter () ->
    c := !c + 1; 
    let letter = if !c >= 26 && letter = None then Some 'v' else letter in
    match letter with
      | Some l ->
        (String.make 1 l) ^ (string_of_int !c)
      | _ ->
        String.make 1 (char_of_int (int_of_char 'a' + !c))

(* Wrap them automatically as type variables *)
let fresh_type_var ?letter (): type_var =
  `Var (fresh_var ?letter ())

(* x, y ::= variable | constant | memory location *)
type ident = [
  `Var of Longident.t
]

(* Create an ident out of a string *)
let ident x = `Var (Longident.Lident x)

(* The mapping from all the bound identifiers in a pattern to the corresponding
 * type variables in the scheme. *)
module IdentMap = Map.Make (struct
  type t = ident
  let compare (`Var x) (`Var y) =
    match x, y with
      | Longident.Lident a, Longident.Lident b -> String.compare a b
      | _ -> fatal_error () "Only simple identifiers are implemented\n"
end)

(* The trick is to use one instance per constructor so that we can use
 * referential equality == to quickly test whether two types are equal. *)
type type_cons = {
  cons_name: string;
  cons_arity: int;
}

(* T ::= X | F \vec{x} *)
type type_term = [
    type_var
  | `Cons of type_cons * type_term list
]

(* (forall x1 x2 ...) * ([ constraint ]) * (mapping from idents to vars) *)
type type_scheme = type_var list * type_constraint * type_var IdentMap.t

(* C, D see p. 407.
 *
 * If there is a pattern on the left-hand side of a let binding, then
 * generate_constraint_pattern will have to bind several identifiers to type
 * variables. This is why we use a IdentMap.
 *
 * We might have more than one type scheme if we use let p1 = e1 and p2 = e2 ...
 *
 * *)
and type_constraint = [
    `True
  | `Conj of type_constraint * type_constraint
  | `Exists of type_var list * type_constraint
  | `Equals of type_term * type_term
  | `Instance of ident * type_term
  | `Let of type_scheme list * type_constraint
  | `Dump
]

(* Instanciate a type constructor with its type variables, thus creating a type
 * term. If the type constructor does not exist, raise an error, unless it's a
 * tuple (all tuples exist, so we create them on demand). *)
let type_cons: string -> type_term list -> type_term =
  let tbl = Hashtbl.create 8 in
  (* Add those ones. They're pre-defined. *)
  Hashtbl.add tbl "->" { cons_name = "->"; cons_arity = 2 };
  Hashtbl.add tbl "int" { cons_name = "int"; cons_arity = 0 };
  Hashtbl.add tbl "char" { cons_name = "char"; cons_arity = 0 };
  Hashtbl.add tbl "string" { cons_name = "string"; cons_arity = 0 };
  Hashtbl.add tbl "float" { cons_name = "float"; cons_arity = 0 };
  (* The function *)
  fun cons_name args ->
    begin match Jhashtbl.find_opt tbl cons_name with
    | Some cons ->
        if List.length args != cons.cons_arity then
          fatal_error () "Bad number of arguments for type constructor %s" cons_name;
        `Cons (cons, args)
    | None ->
        if cons_name = "*" then
          let cons_arity = List.length args in
          let cons_key = "*" ^ (string_of_int cons_arity) in
          match Jhashtbl.find_opt tbl cons_key with
          | None ->
              let cons = { cons_name; cons_arity } in
              Hashtbl.add tbl cons_key cons;
              `Cons (cons, args)
          | Some cons ->
              `Cons (cons, args)
        else
          fatal_error () "Unbound type constructor %s\n" cons_name
    end

let type_cons_arrow x y = type_cons "->" [x; y]
let type_cons_int = type_cons "int" []
let type_cons_char = type_cons "char" []
let type_cons_string = type_cons "string" []
let type_cons_float = type_cons "float" []


