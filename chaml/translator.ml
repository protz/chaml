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

open Algebra.Identifiers

(** This describes a System F variable. *)
type f_var = {
  name: string;
}

(** This describes a System F type. *)
type f_type = f_var Algebra.Core.type_term

(** This is a Sytem F instance. *)
type f_instance = f_type

(** Well, it's the same for a scheme. *)
type f_scheme = f_var list * f_type

type var = [
  | `Var of ident * f_scheme
]

(** The type of Core ASTs *)
type expression = [
  | `Let of pattern * expression * expression 
  | `Instance of ident * f_instance
  | `App of expression * expression list
  | `Lambda of var * expression
  | `Match of expression * (pattern * expression) list
  | `Const of [
      | `Char of char
      | `Int of int
      | `Float of string (** This will have to be converted too *)
      | `String of string
      | `Unit (** This will eventually be removed when we have data types *)]
]
and pattern = [
    var
  | `Tuple of pattern list
  | `Or of pattern * pattern
  | `Any
]

(** Extract an AST based on System F types from the {!Constraint} generator's
    output. *)
let rec extract = function
  | _ -> assert false

(** Translate this AST into the core language. *)
let rec translate = function
  | _ -> assert false
