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

(** Print a constraint (possibly with pretty-printing) in a form suitable for
    parsing by mini. Also provides wrappers for bash colors. *)

(** A pretty-printing environment *)
type pp_env

(** Use this to create a fresh pretty printing environment. *)
val fresh_pp_env : pretty_printing:bool -> unit -> pp_env

(** Color some text using Bash escape sequences. Use like Printf.sprintf. *)
val bash_color : int -> ('a, unit, string, string) format4 -> 'a

(** Convert an identifier into a string. *)
val string_of_ident : [> `Var of Longident.t ] * 'a -> string

(** Convert a constraint into a string. Cannot write
    {Constraint.type_constraint} here because that would create a circular
    dependency. *)
val string_of_constraint :
  pp_env ->
  ([< `Conj of 'a * 'a
    | `Dump
    | `Equals of
        [< `Var of string ] *
        ([< `Cons of Algebra.type_cons * 'b list | `Var of string ] as 'b)
    | `Exists of [< `Var of string ] list * 'a
    | `Instance of ([> `Var of Longident.t ] * 'c) * [< `Var of string ]
    | `Let of
        ([< `Var of string ] list * 'a * [< `Var of string ] Algebra.IdentMap.t) list *
        'a
    | `True
    > `Conj `True ]
   as 'a) ->
  string
