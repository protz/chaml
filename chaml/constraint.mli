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

(** The representation of constraints is defined in this module. *)

(** This module also features, among other things, subtypers {!tv_tt} and
    {!tvl_ttl}, as well as some pretty printers. *)

open Algebra

(** This is a type variable, also known as X in ATTAPL. *)
type type_var = string Algebra.generic_var

(** This is a type, also known as T::= X | F (X1, ... Xn). It can be printed
    using {TypePrinter.string_of_term}.. *)
type type_term = string Algebra.generic_term

(** This main type of constraints. At the moment it is not instanciated anywhere
    else. It should probably be moved here from [Algebra]. *)
type type_constraint = string Algebra.generic_constraint

(** This is a full type scheme. This definition is simplified later on in
    [unify.ml]. Same remark, it is not really general. *)
type type_scheme = string Algebra.generic_scheme

(** We enforce some invariants by requiring that in some places we deal with a
    variable and not a term. However, we often need to subtype. This function
    provides a quick and convenient way to do that. *)
val tv_tt: type_var -> type_term

(** Same wrapper for convenience. *)
val tvl_ttl: type_var list -> type_term list


(** A pretty-printer for constraints. Pretty-prints in a format suitable for
    reading by mini. *)
module PrettyPrinter: sig
  val string_of_type_var: type_var -> string
  val string_of_constraint: pretty_printing:bool -> type_constraint -> string
end