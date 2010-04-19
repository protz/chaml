(*****************************************************************************)
(*  ChaML, a type-checker that uses constraints and a kernel language        *)
(*  Copyright (C) 2010 Jonathan Protzenko                                    *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the ('instance, 'scheme) expressions of the GNU General Public License as published by     *)
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

type ('instance, 'scheme) expression = [
  | `Let of (('instance, 'scheme) pattern * ('instance, 'scheme) expression) list * ('instance, 'scheme) expression
  | `Instance of ident * 'instance
  | `App of ('instance, 'scheme) expression * ('instance, 'scheme) expression list
  | `Lambda of (('instance, 'scheme) pattern * ('instance, 'scheme) expression) list
  | `Match of ('instance, 'scheme) expression * (('instance, 'scheme) pattern * ('instance, 'scheme) expression) list
  | `Const of [
      | `Char of char
      | `Int of int
      | `Float of string
      | `String of string
      | `Unit ]
]
and ('instance, 'scheme) pattern = [
  | `Var of ident * 'scheme
  | `Tuple of ('instance, 'scheme) pattern list
  | `Or of ('instance, 'scheme) pattern * ('instance, 'scheme) pattern
  | `Any
]
