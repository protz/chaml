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

(** This modules transforms the AST obtained from the constraint generator, that
    contains {!Algebra.SOLVER} structures, into a regular AST built on cleaner
    types. The types that were previously [UnionFind] structures are now
    represented using [DeBruijn] indices. [Desugar] will take this
    representation and send it into System F. *)

open Unify
open Algebra.Identifiers

val translate: CamlX.Make(Unify.BaseSolver).expression -> CamlX.f_expression
val string_of_expr: CamlX.f_expression -> string
