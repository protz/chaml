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

type type_var = CamlX.f_type_var
type type_term = CamlX.f_type_term
type type_instance = CamlX.f_instance

type var = [
  | `Var of Atom.t * type_term option
]

type pattern = [
    var
  | `Tuple of pattern list
  | `Or of pattern * pattern
  | `Any
]

type const = [
  | `Char of char
  | `Int of int
  | `Float of float
  | `String of string
  | `Unit
]

type coercion = CamlX.f_coercion

type expression = [
  | `TyAbs of expression
  | `TyApp of expression * type_term
  | `Coerce of expression * coercion

  | `Fun of var * expression
  | `Match of expression * (pattern * expression) list
  | `Let of pattern * expression * expression 
  | `App of expression * expression list

  | `Tuple of expression list
  | `Instance of Atom.t
  | `Const of const
]
