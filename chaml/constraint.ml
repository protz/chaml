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
let string_of_type_var = function
  | `Var s -> s

(* small wrapper *)
let fresh_type_var ?letter (): type_var =
  `Var (fresh_var ?letter ())

(* x, y ::= variable | constant | memory location *)
type ident = [
  `Var of Longident.t
]

(* quick wrapper *)
let ident x = `Var (Longident.Lident x)
let string_of_ident = function
  | `Var (Longident.Lident x) -> x
  | _ -> failwith "This kind of ident is not supported\n"

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

type type_scheme = type_var list * type_constraint * type_var IdentMap.t

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
  | `Equals of type_term * type_term
  | `Instance of ident * type_term
  | `Let of type_scheme list * type_constraint
  | `Dump
]

(* Get a pre-existing type constructor. Create the tuples as needed. *)
let type_cons: string -> type_term list -> type_term =
  let tbl = Hashtbl.create 8 in
  (* Add this one. It's pre-defined. *)
  Hashtbl.add tbl "->" { cons_name = "->"; cons_arity = 2 };
  (* The function *)
  fun cons_name args ->
    begin match Jhashtbl.find_opt tbl cons_name with
    | Some cons ->
        assert ((List.length args) = cons.cons_arity);
        `Cons (cons, args)
    | None ->
        if cons_name = "*" then
          let cons_arity = List.length args in
          let cons_key = "*" ^ (string_of_int cons_arity) in
          match Jhashtbl.find_opt tbl cons_key with
          | None ->
              let cons = { cons_name; cons_arity } in
              Hashtbl.add tbl cons_key cons;
              `Cons (cons, args)
          | Some cons ->
              `Cons (cons, args)
        else
          failwith (Printf.sprintf "Unbound type constructor %s\n" cons_name)
    end

let tv_tt x = (x: type_var :> type_term)

(* Parsetree.pattern 
 *
 * We are given a type var that's supposed to match the given pattern. What we
 * return is a type constraint and a map from identifiers to corresponding type
 * variables. For instance, generate_constraint_pattern X (a*b) returns
 * \exists Y Z. [ X = Y * Z and a < X and b < Y ] and { a => Y; b => Z }
 *
 * *)
let rec generate_constraint_pattern: type_var -> pattern -> (type_constraint * type_var IdentMap.t) =
  fun x { ppat_desc; ppat_loc } ->
    match ppat_desc with
      | Ppat_var v ->
          let var = ident v in
          let var_map = IdentMap.add var x IdentMap.empty in
          `True, var_map
      | Ppat_tuple patterns ->
        (* as in "JIdentMap" *)
        let module JIM = Jmap.Make(IdentMap) in
        let rec combine known_vars known_map current_constraint = function
          | new_pattern :: remaining_patterns ->
              let xi = fresh_type_var () in
              let sub_constraint, sub_map = generate_constraint_pattern xi new_pattern in
              if not (IdentMap.is_empty (JIM.inter known_map sub_map)) then
                failwith "Variable is bound several times in the matching";
              let new_map = JIM.union known_map sub_map in
              let new_constraint = `Conj (sub_constraint, current_constraint) in
              let new_vars = xi :: known_vars in
              combine new_vars new_map new_constraint remaining_patterns
          | [] -> 
              known_vars, known_map, current_constraint
        in
        let sub_vars, sub_map, sub_constraint = combine [] IdentMap.empty `True patterns in
        let sub_vars = (sub_vars: type_var list :> type_term list) in
        let konstraint = `Equals (tv_tt x, type_cons "*" sub_vars) in
        let konstraint = `Conj (konstraint, sub_constraint) in
        konstraint, sub_map
      | _ -> failwith "This pattern is not implemented\n"

(* Parsetree.expression
 * 
 * - TODO figure out what label and the expression option are for in
 * Pexp_function then do things accordingly.
 *
 * *)
and generate_constraint_expression: type_var -> expression -> type_constraint =
  fun t { pexp_desc; pexp_loc } ->
    match pexp_desc with
      | Pexp_function (_, _, pat_expr_list) ->
          let generate_branch (pat, expr) =
            (* as in the definition *)
            let x1 = fresh_type_var ~letter:'x' () in
            let x2 = fresh_type_var ~letter:'x' () in
            (* ~ [[ pat: X1 ]] *)
            let c1, var_map = generate_constraint_pattern x1 pat in
            (* [[ t: X2 ]] *)
            let c2 = generate_constraint_expression x2 expr in
            (* X1 -> X2 = T *)
            let arrow_constr: type_constraint =
              `Equals (type_cons "->" [tv_tt x1; tv_tt x2], (tv_tt t))
            in
            let c2' = `Conj (arrow_constr, c2) in
            let let_constr: type_constraint = `Let ([[], c1, var_map], c2') in
            `Exists ([x1; x2], let_constr)
          in
          let constraints = List.map generate_branch pat_expr_list in
          List.fold_left (fun c1 c2 -> `Conj (c1, c2)) `True constraints
      | Pexp_ident x ->
          `Instance (`Var x, tv_tt t)
      | _ ->
          failwith "This expression is not supported\n"

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
 * The fact that pat_expr_list is there is for let ... and ... that are defined
 * simultaneously. We allow that through the type_scheme list in `Let type.
 *
 * For top-level definitions, the variables end up free in the environment.
 *
 * *)
and generate_constraint: structure -> type_constraint =
  fun structure ->
    let generate_constraint_structure_item = fun { pstr_desc; pstr_loc } c2 ->
      match pstr_desc with
        | Pstr_value (rec_flag, pat_expr_list) ->
            if rec_flag = Asttypes.Nonrecursive then
              let generate_value (pat, expr) =
                let x = fresh_type_var ~letter:'x' () in
                let c1, var_map = generate_constraint_pattern x pat in
                let c1' = generate_constraint_expression x expr in
                [x], `Conj (c1, c1'), var_map
              in
              `Let (List.map generate_value pat_expr_list, c2)
            else
              failwith "rec flag not implemented\n"
        | _ -> failwith "structure_item not implemented\n"
    in
    List.fold_right generate_constraint_structure_item structure `Dump

(* Print the constraints in a format readable by mini *)
let string_of_constraint: type_constraint -> string = fun konstraint ->
  let inc i = " " ^ i in
  let space_before_type_var = fun x -> " " ^ (string_of_type_var x) in
  let rec string_of_constraint = fun i -> function
    | `True ->
        "true"
    | `Conj (`True, c)
    | `Conj (c, `True) ->
        string_of_constraint i c
    | `Conj (c1, c2) ->
        let c1 = string_of_constraint i c1 in
        let c2 = string_of_constraint i c2 in
        String.concat "" ["("; c1; ") and ("; c2; ")"]
    | `Exists (xs, c) ->
        let xs = String.concat "" (List.map space_before_type_var xs) in
        let i' = inc i in
        let c = string_of_constraint i' c in
        String.concat "" ["exists"; xs; ".\n"; i'; c]
    | `Equals (t1, t2) ->
        let t1 = string_of_type t1 in
        let t2 = string_of_type t2 in
        String.concat "" [t1; " = "; t2]
    | `Instance (x, t) ->
        let x = string_of_ident x in
        let t = string_of_type t in
        String.concat "" [x; " < "; t]
    | `Let (schemes, c) ->
        let i' = inc i in
        let sep = ";\n" ^ i' in
        let schemes = String.concat sep (List.map (string_of_type_scheme i') schemes) in
        let c = string_of_constraint i c in
        String.concat "" ("let\n" :: i' :: schemes :: ["\n"; i; "in\n"; i; c])
    | `Dump ->
        "dump\n"
  and string_of_type_scheme i s =
    let open Jstring in
    let xs, c, var_map = s in
    let buf = Buf.create () in
    if List.length xs > 0 then begin
      let xs = List.map space_before_type_var xs in
      Buf.add buf "forall";
      Buf.add_list buf xs;
      Buf.add buf " ";
    end;
    let i' = inc i in
    if c <> `True then begin
      let c = string_of_constraint i' c in
      Buf.add_list buf ["[\n"; i'];
      Buf.add buf c;
      Buf.add_list buf ["\n"; i; "]\n"; i];
    end;
    if not (IdentMap.is_empty var_map) then
      Buf.add buf (string_of_var_map var_map);
    Buf.flush buf
  and string_of_var_map var_map =
    let open Jstring in
    let buf = Buf.create () in
    Buf.add_list buf ["("];
    let l = ref [] in
    IdentMap.iter
      (fun i v ->
        l := (String.concat " : " [string_of_ident i; string_of_type_var v]) :: !l)
      var_map;
    Buf.add buf (String.concat "; " !l);
    Buf.add buf ")";
    Buf.flush buf
  and string_of_type = function
    | `Var _ as v -> string_of_type_var v
    | `Cons ({ cons_name; cons_arity }, types) ->
       match cons_name with
       | "->" as op ->
           let t1 = string_of_type (List.nth types 0) in
           let t2 = string_of_type (List.nth types 1) in
           String.concat " " [t1; op; t2]
       | "*" ->
           let sub_types = List.map string_of_type types in
           String.concat " * " sub_types
       | _ as op ->
           let types = List.map string_of_type types in
           let types = String.concat ", " types in
           String.concat "" [op; "("; types; ")"]
  in
  string_of_constraint "" konstraint

