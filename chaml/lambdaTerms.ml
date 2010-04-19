(*****************************************************************************)
(*  ChaML, a type-checker that uses constraints and a kernel language        *)
(*  Copyright (C) 2010 Jonathan Protzenko                                    *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the expressions of the GNU General Public License as published by     *)
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

module Make (S: Algebra.SOLVER) = struct

  open Algebra.Identifiers

  type expression = [
    | `Let of (pattern * expression) list * expression
    | `Instance of ident * S.instance
    | `App of expression * expression list
    | `Lambda of (pattern * expression) list
    | `Match of expression * (pattern * expression) list
    | `Const of [
        | `Char of char
        | `Int of int
        | `Float of string
        | `String of string
        | `Unit ]
  ]
  and pattern = [
    | `Var of ident * S.scheme
    | `Tuple of pattern list
    | `Or of pattern * pattern
    | `Any
  ]
end
