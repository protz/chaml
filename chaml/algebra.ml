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

(* Now this is for the parameterization of constraint by some solver types *)
module type SOLVER = sig
  type var
  type scheme
  type pscheme
  type instance

  val new_var: string -> var
  val new_scheme_for_var: var -> scheme
  val new_pscheme_for_var: var -> pscheme
  val new_instance: unit -> instance

  val string_of_var: var -> string
end

module Errors = struct

  open Error

  type error =
    | BadNumberOfArguments of string
    | UnboundTypeConstructor of string

  exception Error of error

  let string_of_error = function
    | BadNumberOfArguments s ->
        Printf.sprintf "This constructor has a wrong number of arguments: %s" s
    | UnboundTypeConstructor s ->
        Printf.sprintf "Unbound type constructor %s" s

  let raise_error e = raise (Error e)

end

module Identifiers = struct
  (* x, y ::= variable | constant | memory location *)
  type long_ident =
      Ident of string
    | Dot of long_ident * string
  type ident = long_ident * Location.t

  (* Create an ident out of a string *)
  let ident x pos = Ident x, pos

  (* Get the name *)
  let rec string_of_ident (ident, _loc) =
    let rec string_of_ident = function
    | Ident x -> x
    | Dot (i, x) -> Printf.sprintf "%s.%s" (string_of_ident i) x
    in
    string_of_ident ident

  (* The mapping from all the bound identifiers in a pattern to the corresponding
   * type variables in the scheme. *)
  module IdentMap = Jmap.Make (struct
    type t = ident
    let compare (x, _pos1) (y, _pos2) =
      match x, y with
        | Ident a, Ident b -> String.compare a b
        | _ -> assert false
  end)


  (* Generate globally unique names on demand *)
  let fresh_name =
    let c = ref (-1) in
    fun ?prefix () ->
      c := !c + 1;
      let prefix = if !c >= 26 && prefix = None then Some "v" else prefix in
      let v = match prefix with
        | Some l ->
          l ^ (string_of_int !c)
        | _ ->
          String.make 1 (char_of_int (int_of_char 'a' + !c))
      in
      v
end

module TypeCons = struct

  open Errors

  (* The trick is to use one instance per constructor so that we can use
   * referential equality == to quickly test whether two types are equal. *)
  type type_cons = {
    cons_name: string;
    cons_arity: int;
  }


  (* We have a set of pre-defined types, like the arrow. The ground types are also
   * defined as constructors that take zero arguments. We have discarded int32,
   * int64 and nativeint from OCaml. *)
  let global_constructor_table =
    let tbl = Hashtbl.create 8 in
    Hashtbl.add tbl "->" { cons_name = "->"; cons_arity = 2 };
    Hashtbl.add tbl "int" { cons_name = "int"; cons_arity = 0 };
    Hashtbl.add tbl "char" { cons_name = "char"; cons_arity = 0 };
    Hashtbl.add tbl "string" { cons_name = "string"; cons_arity = 0 };
    Hashtbl.add tbl "float" { cons_name = "float"; cons_arity = 0 };
    Hashtbl.add tbl "unit" { cons_name = "unit"; cons_arity = 0 };
    Hashtbl.add tbl "_bottom" { cons_name = "⊥"; cons_arity = 0 };
    tbl

  (* Instanciate a type constructor with its type variables, thus creating a type
   * term. If the type constructor does not exist, raise an error, unless it's a
   * tuple (all tuples exist, so we create them on demand). *)
  let type_cons =
    fun cons_name args ->
      begin match Jhashtbl.find_opt global_constructor_table cons_name with
      | Some cons ->
          if List.length args <> cons.cons_arity then
            raise_error (BadNumberOfArguments cons_name);
          `Cons (cons, args)
      | None ->
          if cons_name = "*" then
            let cons_arity = List.length args in
            let cons_key = "*" ^ (string_of_int cons_arity) in
            match Jhashtbl.find_opt global_constructor_table cons_key with
            | None ->
                let cons = { cons_name; cons_arity } in
                Hashtbl.add global_constructor_table cons_key cons;
                `Cons (cons, args)
            | Some cons ->
                `Cons (cons, args)
          else
            raise_error (UnboundTypeConstructor cons_name)
      end

  (* That way these constructors are global and we can test type equality by using
   * == (faster) *)
  let type_cons_arrow x y = type_cons "->" [x; y]
  let type_cons_tuple xs = type_cons "*" xs
  let type_cons_int = type_cons "int" []
  let type_cons_char = type_cons "char" []
  let type_cons_string = type_cons "string" []
  let type_cons_float = type_cons "float" []
  let type_cons_unit = type_cons "unit" []
  let type_cons_bottom = type_cons "_bottom" []

end

module Core = struct

  include Errors

  (** This is what is called X in ATTAPL *)
  type 'var type_var = [
    `Var of 'var
  ]

  (** This is what is called T ::= X | F (X1, ..., Xn) in ATTAPL. Used in many
      places. *)
  type 'var type_term = [
      'var type_var
    | `Cons of TypeCons.type_cons * 'var type_term list
  ]

end
