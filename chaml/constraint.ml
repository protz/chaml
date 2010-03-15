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

(* ========== TYPES AND WRAPPERS ========== *)

(* X *)
type type_var = [
  `Var of string
]

let string_of_type_var = function
  | `Var s -> s

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

let fresh_type_var ?letter (): type_var =
  `Var (fresh_var ?letter ())


(* x, y ::= variable | constant | memory location *)
type ident = [
  `Var of Longident.t
]

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


(* ========== CONSTRAINT DUMP ========== *)

(* Useful stuff for coloring matching parentheses with distinct colors. *)
type pp_env = {
  color_stack: int list;
  pretty_printing: bool;
}

let fresh_pp_env ~pretty_printing () = {
  pretty_printing;
  color_stack = [219; 226; 168; 123; 28; 135];
}

let pp_env_step pp_env = match pp_env.color_stack with
  | hd :: tl -> { pp_env with color_stack = tl }
  | [] -> pp_env

let pp_env_brack pp_env s = match pp_env.color_stack with
  | hd :: _ when pp_env.pretty_printing ->
      Printf.sprintf "\x1b[38;5;%dm[\x1b[38;5;15m%s\x1b[38;5;%dm]\x1b[38;5;15m" hd s hd
  | _ ->
      Printf.sprintf "[%s]" s

let pp_env_paren pp_env s = match pp_env.color_stack with
  | hd :: _ when pp_env.pretty_printing ->
      Printf.sprintf "\x1b[38;5;%dm(\x1b[38;5;15m%s\x1b[38;5;%dm)\x1b[38;5;15m" hd s hd
  | _ ->
      Printf.sprintf "(%s)" s

(* Print the constraints in a format readable by mini *)
let string_of_constraint, string_of_type =
  let inc i = " " ^ i in
  let space_before_type_var = fun x -> " " ^ (string_of_type_var x) in
  let rec string_of_constraint pp_env = fun i -> function
    | `True ->
        "true"
    | `Conj (`True, c)
    | `Conj (c, `True)
    | `Conj (c, `Conj (`True, `True))
    | `Conj (`Conj (`True, `True), c) ->
        string_of_constraint pp_env i c
    | `Conj (c1, c2) ->
        let pp_env' = pp_env_step pp_env in
        let c1 = pp_env_paren pp_env (string_of_constraint pp_env' i c1) in
        let c2 = pp_env_paren pp_env (string_of_constraint pp_env' i c2) in
        String.concat "" [c1; " \xE2\x88\xA7 "; c2;]
    | `Exists (xs, c) ->
        let i' = inc i in
        let c = string_of_constraint pp_env i' c in
        if List.length xs > 0 then 
          let xs = String.concat "" (List.map space_before_type_var xs) in
          String.concat "" ["\xE2\x88\x83"; xs; ".\n"; i'; c]
        else
          c
    | `Equals (t1, t2) ->
        let t1 = string_of_type pp_env t1 in
        let t2 = string_of_type pp_env t2 in
        String.concat "" [t1; " = "; t2]
    | `Instance (x, t) ->
        let x = string_of_ident x in
        let t = string_of_type pp_env t in
        String.concat "" [x; " < "; t]
    | `Let (schemes, c) ->
        let i' = inc i in
        let sep = ";\n" ^ i' in
        let schemes = String.concat sep (List.map (string_of_type_scheme pp_env i') schemes) in
        let c = string_of_constraint pp_env i c in
        String.concat "" ("let\n" :: i' :: schemes :: ["\n"; i; "in\n"; i; c])
    | `Dump ->
        "dump\n"
  and string_of_type_scheme pp_env i s =
    let open Jstring in
    let xs, c, var_map = s in
    let buf = Buf.create () in
    if List.length xs > 0 then begin
      let xs = List.map space_before_type_var xs in
      Buf.add buf "\xE2\x88\x80";
      Buf.add_list buf xs;
      Buf.add buf " ";
    end;
    let i' = inc i in
    if c <> `True then begin
      let c = string_of_constraint (pp_env_step pp_env) i' c in
      let tbuf = Buf.create () in
      Buf.add_list tbuf ["\n"; i'];
      Buf.add tbuf c;
      Buf.add_list tbuf ["\n"; i];
      Buf.add buf (pp_env_brack pp_env (Buf.flush tbuf));
      Buf.add buf " ";
    end;
    if not (IdentMap.is_empty var_map) then
      Buf.add buf (string_of_var_map pp_env var_map);
    Buf.flush buf
  and string_of_var_map pp_env var_map =
    let open Jstring in
    let buf = Buf.create () in
    let l = ref [] in
    IdentMap.iter
      (fun i v ->
        l := (String.concat " : " [string_of_ident i; string_of_type_var v]) :: !l)
      var_map;
    Buf.add buf (String.concat "; " !l);
    pp_env_paren pp_env (Buf.flush buf)
  and string_of_type pp_env = function
    | `Var _ as v -> string_of_type_var v
    | `Cons ({ cons_name; cons_arity }, types) ->
       match cons_name with
       | "->" as op ->
           let t1 = string_of_type pp_env (List.nth types 0) in
           let t2 = string_of_type pp_env (List.nth types 1) in
           String.concat " " [t1; op; t2]
       | "*" ->
           let sub_types = List.map (string_of_type pp_env) types in
           String.concat " * " sub_types
       | _ as op ->
           let types = List.map (string_of_type pp_env) types in
           let types = pp_env_paren pp_env (String.concat ", " types) in
           String.concat "" [op; types]
  in
  (* Because of the value restrictiooooooooooon *)
  (fun pp_env konstraint -> string_of_constraint pp_env "" konstraint), string_of_type


(* ========== CONSTRAINT GENERATION ========== *)

let tv_tt x = (x: type_var :> type_term)
let constr_conj = function
  | hd :: tl ->
      List.fold_left (fun x y -> `Conj (x, y)) hd tl
  | _ ->
      assert false

(* Parsetree.pattern 
 *
 * We are given a type var that's supposed to match the given pattern. What we
 * return is a type constraint and a map from identifiers to the corresponding
 * type variables. For instance, generate_constraint_pattern X (a*b) returns
 * \exists Y Z. [ X = Y * Z and a < X and b < Y ] and { a => Y; b => Z }
 *
 * We also return the list of all the variables that have been generated and
 * must be bound existentially for this pattern. The let - binding that encloses
 * us will generate the `Exists constraint for us.
 *
 * NB: one might be tempted to think that the map's keys and the list of
 * existentially bound variables are equal. This is not necessarily true, as we
 * might generate intermediate existential variables that are not bound to a
 * specific identifier.
 *
 * *)
let rec generate_constraint_pattern: type_var -> pattern -> (type_constraint * type_var IdentMap.t * type_var list) =
  fun x { ppat_desc; ppat_loc } ->
    match ppat_desc with
      | Ppat_any ->
          `True, IdentMap.empty, []
      | Ppat_var v ->
          let var = ident v in
          let var_map = IdentMap.add var x IdentMap.empty in
          `True, var_map, []
      | Ppat_tuple patterns ->
        (* as in "JIdentMap" *)
        let module JIM = Jmap.Make(IdentMap) in
        (* This represents the sub patterns. If the pattern is (e1, e2, e3),
         * then we generate x1 x2 x3 such that t = x1 * x2 * x3 *)
        let xis = List.map (fun _ -> fresh_type_var ()) patterns in
        let rec combine known_vars known_map current_constraint_list = function
          | (new_pattern :: remaining_patterns, xi :: xis) ->
              (* sub_vars represents the existential variables that have been
               * generated throughout the pattern *)
              let sub_constraint, sub_map, sub_vars = generate_constraint_pattern xi new_pattern in
              if not (IdentMap.is_empty (JIM.inter known_map sub_map)) then
                failwith "Variable is bound several times in the matching";
              let new_map = JIM.union known_map sub_map in
              let new_constraint_list = sub_constraint :: current_constraint_list in
              (* All the variables that have been generated existentially for
               * this pattern *)
              let new_vars = xi :: sub_vars @ known_vars in
              combine new_vars new_map new_constraint_list (remaining_patterns, xis)
          | ([], []) -> 
              let konstraint = constr_conj current_constraint_list in
              List.rev known_vars, known_map, konstraint
          | _ ->
              assert false
        in
        let pattern_vars, pattern_map, pattern_constraint =
          combine [] IdentMap.empty [] (patterns, xis)
        in
        let xis = (xis: type_var list :> type_term list) in
        let konstraint = `Equals (tv_tt x, type_cons "*" xis) in
        let konstraint = `Conj (konstraint, pattern_constraint) in
        konstraint, pattern_map, pattern_vars
      | Ppat_or (pat1, pat2) ->
        let module JIM = Jmap.Make(IdentMap) in
        let c1, map1, vars1 = generate_constraint_pattern x pat1 in
        let c2, map2, vars2 = generate_constraint_pattern x pat2 in
        let xor_map = JIM.xor map1 map2 in
        if not (IdentMap.is_empty xor_map) then begin
          let bad_ident = List.hd (JIM.keys xor_map) in
          failwith (Printf.sprintf "Variable %s must occur on both sides of this | pattern" (string_of_ident bad_ident))
        end;
        let constraints =
          IdentMap.fold
            (fun k v acc -> `Equals (tv_tt (IdentMap.find k map2), tv_tt v) :: acc)
            map1
            []
        in
        constr_conj (c1 :: c2 :: constraints), map1, vars1 @ vars2
      | _ -> failwith "This pattern is not implemented\n"

(* Parsetree.expression
 * 
 * - TODO figure out what label and the expression option are for in
 * Pexp_function then do things accordingly. label is probably when the argument
 * is labeled. What is the expression option for?
 *
 * *)
and generate_constraint_expression: type_var -> expression -> type_constraint =
  fun t { pexp_desc; pexp_loc } ->
    match pexp_desc with
      | Pexp_function (_, _, pat_expr_list) ->
          (* As in the definition. We could generate fresh variables for each
          * branch of the pattern-matching. The conjunction would then force
          * them to be all equal. However, I find it nicer to share x1 and x2. *)
          let x1 = fresh_type_var ~letter:'x' () in
          let x2 = fresh_type_var ~letter:'x' () in
          let generate_branch (pat, expr) =
            (* ~ [[ pat: X1 ]] *)
            let c1, var_map, generated_vars = generate_constraint_pattern x1 pat in
            (* [[ t: X2 ]] *)
            let c2 = generate_constraint_expression x2 expr in
            (* X1 -> X2 = T *)
            let arrow_constr: type_constraint =
              `Equals (type_cons "->" [tv_tt x1; tv_tt x2], (tv_tt t))
            in
            let c2' = `Conj (arrow_constr, c2) in
            let let_constr: type_constraint = `Let ([[], c1, var_map], c2') in
            (* This allows to properly scope the variables that are inner to
             * each pattern. x1 and x2 are a level higher since they are shared
             * accross patterns. This wouldn't change much as the variables are
             * fresh anyway, but let's do that properly! *)
            `Exists (generated_vars, let_constr)
          in
          let constraints = List.map generate_branch pat_expr_list in
          `Exists ([x1; x2], constr_conj constraints)
      | Pexp_ident x ->
          `Instance (`Var x, tv_tt t)
      | Pexp_apply (e1, label_expr_list) ->
          (* ti: xi *)
          let xis, sub_constraints = List.split
            (List.map
              (fun (_, expr) ->
                let xi = fresh_type_var ~letter:'x' () in
                xi, generate_constraint_expression xi expr
              )
              label_expr_list
            )
          in
          (* build the type constructor t1 -> (t2 -> (... -> (tn -> t))) *)
          let arrow_type = List.fold_right
            (fun c1 c2 -> type_cons "->" [c1; c2])
            (xis: type_var list :> type_term list)
            (tv_tt t)
          in
          (* \exists x1. *)
          let x1 = fresh_type_var ~letter:'x' () in
          (* x1 = t1 -> ... -> tn *)
          let equals_constr: type_constraint = `Equals (tv_tt x1, arrow_type) in
          (* [[ e1: x1 ]] *)
          let arrow_constr = generate_constraint_expression x1 e1 in
          (* combine both: [[ e1: t1 -> t2 -> ... -> tn -> t ]] *)
          let constr: type_constraint = `Conj (arrow_constr, equals_constr) in
          (* the leftmost expression is an arrow and all the arguments have the right type *)
          let konstraint =
            List.fold_left (fun c1 c2 -> `Conj (c1, c2)) constr sub_constraints
          in
          `Exists (x1 :: xis, konstraint)
      | Pexp_let (rec_flag, pat_expr_list, e2) ->
          if rec_flag <> Asttypes.Nonrecursive then
            failwith "Rec flag not supported";
          let c2 = generate_constraint_expression t e2 in
          `Let (List.map generate_constraint_pat_expr pat_expr_list, c2)
      | Pexp_match (e1, pat_expr_list) ->
          let x1 = fresh_type_var ~letter:'x' () in
          let constr_e1 = generate_constraint_expression x1 e1 in
          let generate_branch (pat, expr) =
            let c1, var_map, generated_vars = generate_constraint_pattern x1 pat in
            let c2 = generate_constraint_expression t expr in
            (* XXX Try to generalize here when we have constants.
             * Change `Exists (...) into `Let (generated_vars, ...). Also change
             * the code for Pexp_function *)
            let let_constr: type_constraint = `Let ([[], c1, var_map], c2) in
            `Exists (generated_vars, let_constr)
          in
          let constraints = List.map generate_branch pat_expr_list in
          `Exists ([x1], constr_conj (constr_e1 :: constraints))
      | _ ->
          failwith "This expression is not supported\n"

(* Parsetree.structure
 * 
 * structure_items are only for top-level definitions (modules, types, ...).
 * - Pstr_value is for let x = ...
 * - Pstr_eval is for let _ = ...
 *
 * For let x = ..., we use a fresh type variable T. After constraint resolution
 * is finished, the constraint on T will be the type of the top-level binding we
 * were looking for. The outermost var_map contains the bindings that end up in
 * the environment. A single let-binding can bind multiple variables if the
 * left-hand side is a pattern.
 *
 * The fact that pat_expr_list is a list is because of let ... and ... that are
 * defined simultaneously. We allow that through the type_scheme list in `Let
 * type.
 *
 * For top-level definitions, the variables end up free in the environment.
 *
 * *)
and generate_constraint: structure -> type_constraint =
  fun structure ->
    let generate_constraint_structure_item = fun { pstr_desc; pstr_loc } c2 ->
      match pstr_desc with
        | Pstr_value (rec_flag, pat_expr_list) ->
            if rec_flag <> Asttypes.Nonrecursive then
              failwith "rec flag not implemented\n";
            `Let (List.map generate_constraint_pat_expr pat_expr_list, c2)
        | Pstr_eval expr ->
            let t = fresh_type_var ~letter:'t' () in
            let c = generate_constraint_expression t expr in
            let c = `Exists ([t], c) in
            `Let ([[], c, IdentMap.empty], c2)
        | _ -> failwith "structure_item not implemented\n"
    in
    List.fold_right generate_constraint_structure_item structure `Dump

(* Useful for let pattern = expression ... *)
and generate_constraint_pat_expr: pattern * expression -> type_var list * type_constraint * type_var IdentMap.t =
  fun (pat, expr) ->
    let x = fresh_type_var ~letter:'x' () in
    let c1, var_map, generated_vars = generate_constraint_pattern x pat in
    let c1' = generate_constraint_expression x expr in
    let konstraint = `Exists (generated_vars, `Conj (c1, c1')) in
    [x], konstraint, var_map
