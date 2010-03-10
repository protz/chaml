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

open Parsetree

module StringMap = Map.Make(String)

let fresh_var =
  let c = ref (-1) in
  fun ?letter () ->
    c := !c + 1; 
    let letter = if !c >= 26 && letter = None then Some 'v' else letter in
    match letter with
      | Some l ->
        (String.make 1 l) ^ (string_of_int !c)
      | _ ->
        String.make 1 (char_of_int (int_of_char 'a' + !c))

(* X *)
type type_var = [
  `Var of string
]

(* small wrapper *)
let fresh_type_var ?letter (): type_var =
  `Var (fresh_var ?letter ())

(* x, y ::= variable | constant | memory location *)
type ident = [
  `Var of Longident.t
]

(* quick wrapper *)
let ident x = `Var (Longident.Lident x)

(* Instead of writing
 *   let z: \forall \vec{X}.[C].X in [C']
 * we write
 *   let x1...xn: \forall \vec{X}.[c].X1...XN in [C']
 * and the IdentMap is used to map xi to XI *)
module IdentMap = Map.Make (struct
  type t = ident
  let compare (`Var x) (`Var y) =
    match x, y with
      | Longident.Lident a, Longident.Lident b -> String.compare a b
      | _ -> failwith "Only simple identifiers are implemented\n"
end)

(* T ::= X | F \vec{x} *)
type type_term = [
    type_var
  | `Cons of type_cons * type_term list
]

(* The trick is to use one instance per constructor so that we can use
 * referential equality == to quickly test whether two types are equal. *)
and type_cons = {
  cons_name: string;
  cons_arity: int;
}

type type_scheme = type_var list * type_constraint * type_var IdentMap.t * type_constraint

(* C, D see p. 407.
 *
 * - If there is a pattern on the left-hand side of a let binding, then
 * generate_constraint_pattern will have to bind several identifiers to type
 * variables. This is why we use a IdentMap (see comment above).
 * - `Let is a list because we can bind several identifiers at once using
 * let ...  and ...
 *
 * *)
and type_constraint = [
    `True
  | `Conj of type_constraint * type_constraint
  | `Exists of type_var list * type_constraint
  | `Equals of type_var * type_term
  | `Instance of ident * type_term
  | `Let of type_scheme list
]

(* Wrapper to build T = X -> Y *)
let type_cons_arrow x y: type_term =
  let type_arrow = { cons_name = "->"; cons_arity = 2 } in
  `Cons (type_arrow, [x; y])

(* Wrapper to build T = X * Y *)
let type_term_product x y: type_term =
  let type_product = { cons_name = "*"; cons_arity = 2 } in
  `Cons (type_product, [x; y])

(* Parsetree.pattern *)
let rec generate_constraint_pattern: (type_var * type_constraint * type_var IdentMap.t) -> pattern -> (type_var list * type_constraint * type_var IdentMap.t) =
  fun (x, c, var_map) { ppat_desc; ppat_loc } ->
    match ppat_desc with
      | Ppat_var v ->
          let var = ident v in
          let c' = `Instance (var, (x: type_var :> type_term)) in (* WTF??? *)
          let c'' = `Conj (c, c') in
          let var_map' = IdentMap.add var x var_map in
          [x], c'', var_map'
      (* | Ppat_tuple patterns -> *)
      | _ -> failwith "This pattern is not implemented\n"

(* Parsetree.expression
 * 
 * - TODO figure out what label and the expression option are for in
 * Pexp_function then do things accordingly.
 * *)
and generate_constraint_expression: type_var -> expression -> type_constraint =
  fun x { pexp_desc; pexp_loc } ->
    match pexp_desc with
      | Pexp_function (_, _, pat_expr_list) ->
          let generate_branch pat_expr =
            let t = fresh_type_var ~letter:'t' () in
            let s = generate_scheme t pat_expr in
            let vars, _, _, _ = s in
            t, vars, `Let [s]
          in
          (* for each branch, we get its type variable xi and an associated
          * constraint (it's a `Let [the_type_scheme]) *)
          let type_vars, bound_vars, type_constrs = Jlist.split3 (List.map generate_branch pat_expr_list) in
          let bound_vars = List.flatten bound_vars in
          (* generates x = t1; x = t2; x = ... *)
          let equalities: type_constraint list = List.map (fun t -> `Equals (x, (t: type_var :> type_term))) type_vars in
          (* do a big `Conj of a list *)
          let conj = List.fold_left (fun c1 c2 -> `Conj (c1, c2)) `True in
          (* generates c1 \wedge c2 \wedge ... \wedge cn *)
          let constraints1 = conj type_constrs in
          let constraints2 = conj equalities in
          `Exists (bound_vars , `Conj (constraints1, constraints2))
      | Pexp_ident i ->
          `Instance (`Var i, (x: type_var :> type_term)) (* WTF??? *)
      | _ ->
          failwith "This expression is not supported\n"

(* Parsetree.pattern = Parsetree.expression --> generate scheme
 *
 * Maybe as an optimization we would like to keep the IdentMap all along the
 * way, pass it from function to function, and then be able to lookup in it
 * anywhere. Plus it's functional so its matches the recursive calls...
 *
 * *)
and generate_scheme: type_var -> (pattern * expression) -> type_scheme = fun t (pat, expr) ->
  let x = fresh_type_var ~letter:'x' () in
  let type_vars, c1, var_map = generate_constraint_pattern (x, `True, IdentMap.empty) pat in
  let c2 = generate_constraint_expression t expr in
  x::type_vars, c1, var_map, c2

(* Parsetree.structure_item
 * 
 * structure_items are only for top-level definitions (modules, types, ...).
 * - Pstr_value is for let x = ...
 * - Pstr_eval is for let _ = ...
 *
 * For let x = ..., we use a fresh type variable T. After constraint resolution
 * is finished, the constraint on T will be the type of the top-level binding we
 * were looking for. It's quite unclear for the moment how we'll do that but
 * let's leave it like that.
 *
 * *)
and generate_constraint_structure_item: type_var -> structure_item -> type_constraint =
  fun t { pstr_desc; pstr_loc } ->
    match pstr_desc with
      | Pstr_value (rec_flag, pat_expr_list) ->
          if rec_flag = Asttypes.Nonrecursive then
            let generate_fresh pat_expr =
              let t = fresh_type_var ~letter:'t' () in
              generate_scheme t pat_expr
            in
            `Let (List.map generate_fresh pat_expr_list)
          else
            failwith "rec flag not implemented\n"
      | _ -> failwith "structure_item not implemented\n"

(* Generate a constraint for a given program *)
let generate_constraint: structure -> type_constraint list =
  fun structure ->
    let f structure_item = generate_constraint_structure_item (fresh_type_var ~letter:'t' ()) structure_item in
    List.map f structure

(* Print the constraints in a format readable by mini *)
let string_of_constraint konstraint: string =
  assert false
