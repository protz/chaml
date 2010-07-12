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

(** Defines two types of eXplicitely typed Caml ASTs: {!Make.expression} that
    contains the solver structures, and {!f_expression} that is the result of
    {!Translator} and has {!DeBruijn} types instead. *)

(** For convenience, and to follow what the constraint generator does more
   closely, we use a functor for the first type. *)

open Algebra.Identifiers

module Make (S: Algebra.SOLVER): sig

  type user_type_var = int
  type user_type_term = user_type_var Algebra.Core.type_term
  type user_type_kind = [ `Variant | `Record ]
  type user_label = string
  type user_type = <
    name: string;
    arity: int;
    kind: user_type_kind;
    fields: (user_label * user_type_term list) list;
  >

  type expression = [
    | `Let of bool * (pattern * S.pscheme * expression) list * expression 
        (** The boolean is true if this is recursive *)
    | `Instance of ident * S.instance
    | `App of expression * expression list
    | `Function of S.pscheme * (pattern * expression) list
        (** This one doesn't generalize so we have the invariant that the young
          * variables list of the pscheme is empty. *)
    | `Match of expression * S.pscheme * (pattern * S.pscheme option * expression) list
        (** The is the most general(izing) match. There is [Some pscheme] if
          * this is generalizing match and the expression that's returned is
          * polymorphic. As we're taking an instance, we need this to be able to
          * rebuild the F-term properly. *)
    | `Tuple of expression list
    | `Construct of string * S.var list * user_label * expression list
        (** The string is the type's name.
            The S.var list are the type variables for this data type. *)
    | `Const of const
    | `Sequence of expression * expression
    | `IfThenElse of expression * expression * expression option
    | `AssertFalse
    | `Magic (** For builtins, gets a special treatment later on *)
  ]
  and pattern = [
    | `Var of ident
    | `Tuple of pattern list
    | `Or of pattern * pattern
    | `Const of const
    | `Any
    | `Construct of user_label * pattern list
    | `Alias of pattern * ident
  ]
  and const = [
    | `Char of char
    | `Int of int
    | `Float of string
    | `String of string
  ]

  type structure_item = [
    | `Let of bool * (pattern * S.pscheme * expression) list
    | `Type of user_type
  ]

  type structure = structure_item list

end

type f_type_term = [
    DeBruijn.type_var
  | `Cons of Algebra.TypeCons.head_symbol * f_type_term list
  | `Forall of f_type_term
]

(* We're accepting `Forall because we might want polymorphic record fields at
 * some point.. *)
type f_user_type_term = f_type_term
type f_user_type_kind = [ `Variant | `Record ]
type f_user_label = string
type f_user_type = <
  name: string;
  arity: int;
  kind: f_user_type_kind;
  fields: (f_user_label * f_user_type_term list) list;
>

type f_instance = f_type_term list

type f_expression = [
  | `Let of bool * (f_pattern * f_clblock * f_expression) list * f_expression 
  | `Instance of ident * f_instance
  | `App of f_expression * f_expression list
      (** Maybe we can simplify this later on (do we really want it?) *)
  | `Function of f_type_term * (f_pattern * f_expression) list
      (** All patterns have the same type because we're in ML. This later
         desugars to a `Fun and a `Match. We need the f_type_term to annotate
         the argument of the `Fun. *)
  | `Match of f_expression * f_clblock * (f_pattern * f_expression) list
      (** The f_clblock is necessary to properly generate the various coercions
         needed for each branch of the generalizing match. **)
  | `Tuple of f_expression list
  | `Construct of string * f_type_term list * f_user_label * f_expression list
  | `Sequence of f_expression * f_expression
  | `IfThenElse of f_expression * f_expression * f_expression option
  | `AssertFalse
  | `Const of f_const
  | `Magic of f_type_term
      (** For builtins, gets a special treatment later on *)
]
and f_pattern = [
  | `Var of ident
  | `Tuple of f_pattern list
  | `Or of f_pattern * f_pattern
  | `Const of f_const
  | `Construct of f_user_label * f_pattern list
  | `Alias of f_pattern * ident
  | `Any
]
and f_const = [
  | `Char of char
  | `Int of int
  | `Float of string
      (** This will have to be converted too *)
  | `String of string
]
and f_clblock = {
  young_vars: int;
  f_type_term: f_type_term;
}

type f_structure_item = [
  | `Let of bool * (f_pattern * f_clblock * f_expression) list
  | `Type of f_user_type
]

type f_structure = f_structure_item list
