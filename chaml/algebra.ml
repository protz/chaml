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

(* x, y ::= variable | constant | memory location *)
type long_ident =
    Ident of string
  | Dot of long_ident * string
type ident = long_ident * Location.t

(* Create an ident out of a string *)
let ident x pos = Ident x, pos

(* Get the name *)
let rec string_of_ident (ident, _loc) =
  let rec string_of_ident = function
  | Ident x -> x
  | Dot (i, x) -> Printf.sprintf "%s.%s" (string_of_ident i) x
  in
  string_of_ident ident

(* The mapping from all the bound identifiers in a pattern to the corresponding
 * type variables in the scheme. *)
module IdentMap = Map.Make (struct
  type t = ident
  let compare (x, pos1) (y, pos2) =
    match x, y with
      | Ident a, Ident b -> String.compare a b
      | _ -> fatal_error "Only simple identifiers are implemented\n"
end)


(* Generate globally unique names on demand *)
let fresh_name =
  let c = ref (-1) in
  fun ?prefix () ->
    c := !c + 1;
    let prefix = if !c >= 26 && prefix = None then Some "v" else prefix in
    let v = match prefix with
      | Some l ->
        l ^ (string_of_int !c)
      | _ ->
        String.make 1 (char_of_int (int_of_char 'a' + !c))
    in
    v


(* The trick is to use one instance per constructor so that we can use
 * referential equality == to quickly test whether two types are equal. *)
type type_cons = {
  cons_name: string;
  cons_arity: int;
}

(* X *)
type 'var_type generic_var = [
  `Var of 'var_type
]

(* T ::= X | F \vec{x} *)
type 'var_type generic_term = [
    'var_type generic_var
  | `Cons of type_cons * 'var_type generic_term list
]

(* (forall x1 x2 ...) * ([ constraint ]) * (mapping from idents to vars)
 *
 * If there is a pattern on the left-hand side of a let binding, then
 * generate_constraint_pattern will have to bind several identifiers to type
 * variables. This is why we use a IdentMap.
 *
 * *)
type 'var_type generic_scheme =
    'var_type generic_var list
  * 'var_type generic_constraint
  * 'var_type generic_var IdentMap.t

(* C, D see p. 407.
 *
 * We might have more than one type scheme if we use let p1 = e1 and p2 = e2 ...
 * which is why we use a type_scheme list in the `Let branch.
 *
 * *)
and 'var_type generic_constraint = [
    `True
  | `Conj of 'var_type generic_constraint * 'var_type generic_constraint
  | `Exists of 'var_type generic_var list * 'var_type generic_constraint
  | `Equals of 'var_type generic_var * 'var_type generic_term
  | `Instance of ident * 'var_type generic_var
  | `Let of 'var_type generic_scheme list * 'var_type generic_constraint
  | `Dump
]


(* We have a set of pre-defined types, like the arrow. The ground types are also
 * defined as constructors that take zero arguments. We have discarded int32,
 * int64 and nativeint from OCaml. *)
let global_constructor_table =
  let tbl = Hashtbl.create 8 in
  Hashtbl.add tbl "->" { cons_name = "->"; cons_arity = 2 };
  Hashtbl.add tbl "int" { cons_name = "int"; cons_arity = 0 };
  Hashtbl.add tbl "char" { cons_name = "char"; cons_arity = 0 };
  Hashtbl.add tbl "string" { cons_name = "string"; cons_arity = 0 };
  Hashtbl.add tbl "float" { cons_name = "float"; cons_arity = 0 };
  Hashtbl.add tbl "unit" { cons_name = "unit"; cons_arity = 0 };
  tbl

(* Instanciate a type constructor with its type variables, thus creating a type
 * term. If the type constructor does not exist, raise an error, unless it's a
 * tuple (all tuples exist, so we create them on demand). *)
let type_cons =
  fun cons_name args ->
    begin match Jhashtbl.find_opt global_constructor_table cons_name with
    | Some cons ->
        if List.length args != cons.cons_arity then
          fatal_error "Bad number of arguments for type constructor %s" cons_name;
        `Cons (cons, args)
    | None ->
        if cons_name = "*" then
          let cons_arity = List.length args in
          let cons_key = "*" ^ (string_of_int cons_arity) in
          match Jhashtbl.find_opt global_constructor_table cons_key with
          | None ->
              let cons = { cons_name; cons_arity } in
              Hashtbl.add global_constructor_table cons_key cons;
              `Cons (cons, args)
          | Some cons ->
              `Cons (cons, args)
        else
          fatal_error "Unbound type constructor %s\n" cons_name
    end

(* That way these constructors are global and we can test type equality by using
 * == (faster) *)
let type_cons_arrow x y = type_cons "->" [x; y]
let type_cons_int = type_cons "int" []
let type_cons_char = type_cons "char" []
let type_cons_string = type_cons "string" []
let type_cons_float = type_cons "float" []
let type_cons_unit = type_cons "unit" []
