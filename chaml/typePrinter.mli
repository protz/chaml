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

(** Print types from the Algebra module. [Unify] provides wrappers over these
    functions to properly convert from a unification var to a ['a, 'b, ...] var.
  *)

open Algebra

(** This type represents a disambiguated type, that is, where all cycles have
    been converted to [`Alias]es. [Unify] has a function called [inspect_var]
    that converts a unification variable to such a variable. The tests output
    directly a [inspected_var]. *)
type 'var inspected_var = [
    'var generic_var
  | `Cons of type_cons * 'var inspected_var list
  | `Alias of 'var inspected_var * 'var generic_var
]

(** The [string_of_key] optional argument tells how to convert from a ['var] to
    a string. If it's a unification var, one might want to use the internal name
    for debugging. *)
val string_of_type: ?string_of_key:('var -> string) -> ?caml_types:bool -> ?young_vars:'var list-> 'var inspected_var -> string

(** This function is useful for generating error messages. It does not create
    fresh variables for each term; instead, all unification variables are
    assigned a unique name accross the inspected_vars. Instead of ["cannot unify
    'a with 'a * 'b"], you get ["cannot unify 'a with 'b * 'c"]. *)
val string_of_types: ?string_of_key:('var -> string) -> ?caml_types:bool -> ?young_vars:'var list list -> 'var inspected_var list -> string list

(** Just a type-converted function for printing Algebra's generic terms. Useful
    for error messages. *)
val string_of_term: 'a Algebra.generic_term -> string
