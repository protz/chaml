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

type f_type_var = { index: int; }
type type_var = f_type_var Algebra.Core.type_var
type type_term = [
    type_var
  | `Cons of Algebra.TypeCons.type_cons * type_term list
  | `Forall of type_term
]

type type_instance = f_type_var list
type type_scheme = f_type_var list * type_term
type t = (type_instance, type_scheme) CamlX.expression

module DeBruijn = struct
  let lift: int -> type_term -> type_term =
    fun _ _ -> assert false

  let subst: type_term -> f_type_var -> type_term =
    fun _ _ -> assert false
end

let translate _ =
  `Const (`Int 42)

let string_of_t =
  fun _ -> assert false
