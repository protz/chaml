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

(** An explicitely typed AST (eXplicit Caml). The ['instance] and ['scheme] type
    parameters are initially those of the Solver. Module {!Translator} turns
    these into F types with De Bruijn indices. *)

(** The constraint generator generates a constraint as well as a {!expression}
    that represents a well-typed AST when the solving is done. *)

open Algebra.Identifiers

type ('instance, 'scheme, 'var) expression = [
  | `Let of
        (('instance, 'scheme) pattern * ('instance, 'scheme, 'var) expression) list
      * 'var list ref
      * ('instance, 'scheme, 'var) expression 
  | `Instance of ident * 'instance
  | `App of ('instance, 'scheme, 'var) expression * ('instance, 'scheme, 'var) expression list (** Maybe we can simplify this later on (do we really want it?) *)
  | `Lambda of (('instance, 'scheme) pattern * ('instance, 'scheme, 'var) expression) list (** This will be converted later on to a simple form that uses `Match. *)
  | `Match of ('instance, 'scheme, 'var) expression * (('instance, 'scheme) pattern * ('instance, 'scheme, 'var) expression) list
  | `Tuple of ('instance, 'scheme, 'var) expression list
  | `Const of [
      | `Char of char
      | `Int of int
      | `Float of string (** This will have to be converted too *)
      | `String of string
      | `Unit (** This will eventually be removed when we have data types *)]
]
and ('instance, 'scheme) pattern = [
  | `Var of ident * 'scheme
  | `Tuple of ('instance, 'scheme) pattern list
  | `Or of ('instance, 'scheme) pattern * ('instance, 'scheme) pattern
  | `Any
]
