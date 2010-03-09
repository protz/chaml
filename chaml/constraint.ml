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

module StringMap = Map.Make(String)

let fresh_var () =
  let c = ref (-1) in
  c := !c + 1;
  if !c > 26 then
    "v" ^ (string_of_int !c)
  else
    String.make 1 (char_of_int (int_of_char 'a' + !c))

(* X *)
type type_var = [
  | `Var of string
]
(* T ::= X | F \vec{x} *)
type type_term = [
    type_var
  | `Cons of string * int * type_term list
]
(* σ ::= \forall \vec{X} [C] T *)
and type_scheme = [
  | `Forall of type_var list * type_constraint * type_term
]
(* x, y ::= variable | constant | memory location *)
and ident = [
  | `Var of string
]
(* C, D see p. 407 *)
and type_constraint = [
  | `True
  | `Conj of type_constraint * type_constraint
  | `Exists of type_var list * type_constraint
  | `Instance of ident * type_term
  | `Let of ident * type_scheme * type_constraint
]

(* Wrapper to build T = X -> Y *)
let type_term_arrow x y: type_term =
  `Cons ("->", 2, [x; y])

(* Wrapper to build T = X * Y *)
let type_term_product x y: type_term =
  `Cons ("*", 2, [x; y])

(* Wrapper to build a type scheme σ = X *)
let type_scheme_var v: type_scheme =
  `Forall ([], `True, `Var v)

(* Generate a constraint for a given program *)
let generate_constraint ast: type_constraint =
  assert false

(* Print the constraints in a format readable by mini *)
let string_of_constraint konstraint: string =
  assert false
