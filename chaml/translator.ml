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

open Algebra.Identifiers
open Unify
open CamlX
(* Don't do this, kids. Works because this functor is applicative. *)
module rec CamlX_: module type of CamlX.Make(BaseSolver) = CamlX_
open CamlX_

(* Various helpers to work with environments *)

module IntMap = Jmap.Make(struct
  type t = int
  let compare = compare
end)

type env = {
  fvar_of_uvar: DeBruijn.t IntMap.t;
}

let lift_add env uvar =
  let new_map =
    IntMap.map DeBruijn.lift_t env.fvar_of_uvar
  in
  let new_map =
    IntMap.add (id uvar) DeBruijn.zero new_map
  in
  Error.debug "[TLiftAdd] Adding %a\n" uvar_name uvar;
  { fvar_of_uvar = new_map }

let concat f l =
  List.fold_left f (List.hd l) (List.tl l)

(* Once all the right variables are in the environment, we simply transcribe a
 * scheme into the right fscheme structure (it's a f_type_term) *)
let type_term_of_uvar env uvar =
  let rec type_term_of_uvar uvar =
    let repr = find uvar in
    match repr.term with
    | None ->
        let fvar = IntMap.find repr.id env.fvar_of_uvar in
        `Var fvar
    | Some (`Cons (cons_name, cons_args)) ->
        `Cons (cons_name, List.map type_term_of_uvar cons_args)
  in
  type_term_of_uvar uvar 

(* The core functions *)

exception Magic

let translate =
  let rec translate_expr: env -> expression -> f_expression = 
    fun env uexpr ->
    match uexpr with
      | `Let (rec_flag, pat_expr_list, e2) ->
          translate_pat_expr_list
            env rec_flag pat_expr_list
            (fun pat_expr_list ->
              let fexpr = translate_expr env e2 in
              `Let (rec_flag, pat_expr_list, fexpr))

      | `Function (pscheme, pat_expr_list) ->
           let pat_expr_list = List.map
            (fun (upat, uexpr) ->
              let fpat = translate_pat env upat in
              let fexpr = translate_expr env uexpr in
              fpat, fexpr
            )
            pat_expr_list
          in
          let type_term = type_term_of_uvar env pscheme.p_uvar in
          `Function (type_term, pat_expr_list)

      | `Instance (ident, instance) ->
          let instance = List.map (type_term_of_uvar env) !instance in
          Error.debug
            "[TInstance] Instanciating %s scheme with %d variables\n"
            (string_of_ident ident)
            (List.length instance);
          `Instance (ident, instance)

      | `App (e1, args) ->
          `App (translate_expr env e1, List.map (translate_expr env) args)

      | `Match (expr, pscheme, pat_exprs) ->
          (* C/Pasted from `Let: generalize expr properly *)
          let new_env = List.fold_left lift_add env pscheme.p_young_vars in
          let f_type_term = type_term_of_uvar new_env pscheme.p_uvar in
          let young_vars = List.length pscheme.p_young_vars in
          Error.debug "[TMatch] %d generalized variables\n" young_vars;
          let clblock = {
            young_vars;
            f_type_term;
          } in
          let fexpr = translate_expr new_env expr in
          (* Generate patterns and expressions properly *)
          let gen (pat, pscheme, expr) =
            let fpat = translate_pat env pat in
            let fexpr = translate_expr env expr in
            begin match pscheme with
              | Some pscheme ->
                  assert (List.length pscheme.p_young_vars = young_vars);
              | None ->
                  assert (young_vars = 0)
            end;
            fpat, fexpr
          in
          let pat_exprs = List.map gen pat_exprs in
          `Match (fexpr, clblock, pat_exprs)

      | `Tuple (exprs) ->
          `Tuple (List.map (translate_expr env) exprs)

      | `Construct (c, exprs) ->
          `Construct (c, List.map (translate_expr env) exprs)

      | `Const _ as x ->
          x

      | `Sequence _ ->
          failwith "ToDo implement sequence in translator.ml"

      | `IfThenElse _ ->
          failwith "ToDo implement ifthenelse in translator.ml"

      | `AssertFalse ->
          failwith "ToDo implement assert false in translator.ml"

      | `Magic ->
          raise Magic

  and translate_pat_expr_list: 'a.
        env ->
        bool ->
        (pattern * BaseSolver.pscheme * expression) list ->
        ((f_pattern * f_clblock * f_expression) list -> 'a) ->
        'a
     = fun env rec_flag pat_expr_list k ->
    (* This is a convention: in the case of a recursive let, the scheme
     * variables are shared across all the identifiers' types and they are
     * stored in the first identifiers pscheme. *)
    let rec_scheme_vars =
      let _, pscheme, _ = List.hd pat_expr_list in
      pscheme.p_young_vars
    in
    let pat_expr_list =
      List.map
        (fun (upat, pscheme, uexpr) ->
          (* The patterns are translated in the current environment *)
          let fpat = translate_pat env upat in
          (* Then we move to the rigt of let p1 = e1, this is where we
           * introduce the new type variables *)
          let young_vars =
            if rec_flag then
              rec_scheme_vars
            else
              pscheme.p_young_vars
          in
          let new_env = List.fold_left lift_add env young_vars in
          let f_type_term = type_term_of_uvar new_env pscheme.p_uvar in
          let young_vars = List.length young_vars in
          Error.debug "[TScheme] %d variables in this pattern\n" young_vars;
          let clblock = {
            young_vars;
            f_type_term;
          } in
          let fexpr =
            try
              translate_expr new_env uexpr
            with Magic ->
              `Magic f_type_term
          in
          (fpat, clblock, fexpr)
        )
        pat_expr_list
    in
    k pat_expr_list

  (* [translate_pat] just generates patterns as needed. It doesn't try to
   * assign schemes to variables if those are on the left-hand side of a pattern. *)
  and translate_pat: env -> pattern -> f_pattern =
    fun _env upat ->
      (upat: pattern :> f_pattern)
    (* match upat with
      | `Any as r ->
          r

      | `Const c ->
          `Const c

      | `Tuple patterns ->
          `Tuple (List.map (translate_pat env) patterns)

      | `Or (p1, p2) ->
          `Or (translate_pat env p1, translate_pat env p2)

      | `Var ident ->
          `Var ident

      | `Construct (c, pats) ->
          `Construct (c, List.map (translate_pat env) pats) *)

  (* The thing is here, we're only renaming types, and types of top-level
   * bindings are closed, so there's nothing to forward across structure items.
   * However, when we desugar, the bindings above the current top-level binding
   * must be made available, so then we'll use something like a fold_left
   * instead of a map. *)
  and translate_struct: env -> structure_item -> f_structure_item =
    fun env ustr ->
      match ustr with
      | `Let (rec_flag, pat_expr_list) ->
          translate_pat_expr_list
            env rec_flag pat_expr_list
            (fun pat_expr_list ->
              `Let (rec_flag, pat_expr_list))
      | `Type _ ->
          failwith "TODO: implement type decls in translator.ml"

  in

  List.map (fun x -> translate_struct { fvar_of_uvar = IntMap.empty } x)

(* Just generate as many uppercase lambdas as needed *)
let make lambda n = 
  let open Bash in
  let open Pprint in
  let lambdas = String.concat "" (Jlist.make n lambda) in
  let lambdas = color colors.blue "%s" lambdas in
  let lambdas = fancystring lambdas n in
  lambdas

let gen_lambdas = make "Λ"

(* Pretty-printing stuff *)
let rec doc_of_expr: f_expression -> Pprint.document = 
  let open Pprint in
  let open Bash in
  function
    | `Let (rec_flag, pat_expr_list, e2) ->
        let gen (pat, { young_vars = nlambdas; f_type_term = scheme }, expr) =
          let pdoc = doc_of_pat pat in
          let edoc = doc_of_expr expr in
          let lb' = fancystring (color colors.blue "[") 1 in
          let rb' = fancystring (color colors.blue "]") 1 in
          let ldoc = gen_lambdas nlambdas in
          let fdoc =
            if nlambdas > 0 then
              (make "∀" nlambdas) ^^ dot ^^ space
            else
              empty
          in
          let scheme = string (DeBruijn.string_of_type_term scheme) in
          pdoc ^^ colon ^^ space ^^
          fdoc ^^ lb' ^^ scheme ^^ rb' ^^ space ^^ equals ^^
          space ^^ ldoc ^^
            (nest 2 (break1 ^^ edoc)
          )
        in
        let pat_expr_list = List.map gen pat_expr_list in
        let anddoc = fancystring (color 208 "and") 3 in
        let pat_expr_list = concat
          (fun x y -> x ^^ break1 ^^ anddoc ^^ space ^^ y)
          pat_expr_list
        in
        let e2 = doc_of_expr e2 in
        let letdoc = fancystring (color 208 "let") 3 in
        let indoc = fancystring (color 208 "in") 2 in
        let recdoc = if rec_flag then string "rec " else empty in
        letdoc ^^ space ^^ recdoc ^^ pat_expr_list ^^ break1 ^^
        indoc ^^ break1 ^^
        e2

    | `Function (type_term, pat_expr_list) ->
        (* type_term of the argument as a whole; it might be a pattern so
         * we have the type of the whole first argument. This is needed for
         * [Desugar] to translate this `Function into a `Fun (`Match...) *)
        let tdoc = string (DeBruijn.string_of_type_term type_term) in
        if (List.length pat_expr_list > 1) then
          let gen (pat, expr) =
            let pdoc = doc_of_pat pat in
            let edoc = doc_of_expr expr in
            bar ^^ space ^^ lparen ^^ pdoc ^^ colon ^^ space ^^ tdoc ^^
            rparen ^^ space ^^ minus ^^ rangle ^^ (nest 4 (break1 ^^ edoc))
          in
          let pat_expr_list = List.map gen pat_expr_list in
          let pat_expr_list = concat
            (fun x y -> x ^^ hardline ^^ y)
            pat_expr_list
          in
          (string "function") ^^ (nest 2 (hardline ^^ pat_expr_list))
        else
          let pat, expr = List.hd pat_expr_list in
          let pdoc = doc_of_pat pat in
          let edoc = doc_of_expr expr in
          (string "fun") ^^ space ^^ lparen ^^ pdoc ^^ colon ^^ space ^^
          tdoc ^^ rparen ^^ space ^^ minus ^^ rangle ^^ space ^^ edoc

    | `Instance (ident, instance) ->
        let ident = string (string_of_ident ident) in
        if List.length instance > 0 then
          let instance = List.map (fun x -> string (DeBruijn.string_of_type_term x)) instance in
          let instance = concat (fun x y -> x ^^ comma ^^ space ^^ y) instance in
          let lb = fancystring (color colors.red "[") 1 in
          let rb = fancystring (color colors.red "]") 1 in
          ident ^^ space ^^ lb ^^ instance ^^ rb
        else
          ident

    | `App (e1, args) ->
        concat (fun x y -> x ^^ space ^^ y) (List.map doc_of_expr (e1 :: args))

    | `Match (expr, { young_vars; f_type_term }, pat_expr_list) ->
        let ldoc = gen_lambdas young_vars in
        let lb' = fancystring (color colors.blue "[") 1 in
        let rb' = fancystring (color colors.blue "]") 1 in
        let scheme = string (DeBruijn.string_of_type_term f_type_term) in
        let gen (pat, expr) =
          let pdoc = doc_of_pat pat in
          let edoc = doc_of_expr expr in
          bar ^^ space ^^ pdoc ^^ space ^^ minus ^^ rangle ^^
            (nest 4 (break1 ^^ edoc)
          )
        in
        let pat_expr_list = List.map gen pat_expr_list in
        let pat_expr_list = concat
          (fun x y -> x ^^ break1 ^^ y)
          pat_expr_list
        in
        let matchdoc = fancystring (color 208 "match") 5 in
        let exprdoc = doc_of_expr expr in
        let withdoc = fancystring (color 208 "with") 4 in
        matchdoc ^^ space ^^ exprdoc ^^ colon ^^ space ^^
        ldoc ^^ dot ^^ space ^^ lb' ^^ scheme ^^ rb' ^^ space ^^
        withdoc ^^ break1 ^^
        pat_expr_list

    | `Tuple (exprs) ->
        (* XXX compute operator priorities cleanly here *)
        let paren_if_needed = function
          | `Function _ as l ->
              lparen ^^ (doc_of_expr l) ^^ rparen
          | x ->
              doc_of_expr x
        in
        let edocs = List.map paren_if_needed exprs in
        let edoc = concat (fun x y -> x ^^ comma ^^ space ^^ y) edocs in
        lparen ^^ edoc ^^ rparen

    | `Const c ->
        doc_of_const c

    | `Construct _ ->
        failwith "TODO: implement construct pretty-printing in translator"

    | `Magic t ->
        (string "%magic: ") ^^ (string (DeBruijn.string_of_type_term t))

and doc_of_pat: f_pattern -> Pprint.document =
  let open Pprint in
  function
    | `Any ->
        underscore

    | `Tuple patterns ->
        let pdocs = List.map doc_of_pat patterns in
        let pdoc = concat (fun x y -> x ^^ comma ^^ space ^^ y) pdocs in
        lparen ^^ pdoc ^^ rparen

    | `Or (p1, p2) ->
        let pdoc1 = doc_of_pat p1 in
        let pdoc2 = doc_of_pat p2 in
        pdoc1 ^^ space ^^ bar ^^ space ^^ pdoc2

    | `Construct _ ->
        failwith "TODO: pretty-print construct patterns"

    | `Const c ->
        doc_of_const c

    | `Alias _ ->
        failwith "TODO pretty-print pattern alias in translator"

    | `Var ident ->
        string (string_of_ident ident)

and doc_of_const: f_const -> Pprint.document =
  let open Pprint in
  function
    | `Char c ->
        string (String.make 1 c)
    | `Int i ->
        string (string_of_int i)
    | `Float f ->
        string f
    | `String s ->
        dquote ^^ (string s) ^^ dquote

and doc_of_struct: f_structure -> Pprint.document =
  let open Pprint in
  let open Bash in
  let doc_of_str: f_structure_item -> Pprint.document =
    function
    | `Let (rec_flag, pat_expr_list) ->
        let gen (pat, { young_vars = nlambdas; f_type_term = scheme }, expr) =
          let pdoc = doc_of_pat pat in
          let edoc = doc_of_expr expr in
          let lb' = fancystring (color colors.blue "[") 1 in
          let rb' = fancystring (color colors.blue "]") 1 in
          let ldoc = gen_lambdas nlambdas in
          let fdoc =
            if nlambdas > 0 then
              (make "∀" nlambdas) ^^ dot ^^ space
            else
              empty
          in
          let scheme = string (DeBruijn.string_of_type_term scheme) in
          pdoc ^^ colon ^^ space ^^
          fdoc ^^ lb' ^^ scheme ^^ rb' ^^ space ^^ equals ^^
          space ^^ ldoc ^^
            (nest 2 (break1 ^^ edoc)
          )
        in
        let pat_expr_list = List.map gen pat_expr_list in
        let anddoc = fancystring (color 208 "and") 3 in
        let pat_expr_list = concat
          (fun x y -> x ^^ break1 ^^ anddoc ^^ space ^^ y)
          pat_expr_list
        in
        let letdoc = fancystring (color 208 "let") 3 in
        let recdoc = if rec_flag then string "rec " else empty in
        letdoc ^^ space ^^ recdoc ^^ pat_expr_list

    | `Type _ ->
        failwith "TODO: pretty-printing type decls in Core"
  in
  fun str ->
    let l = List.map doc_of_str str in
    concat (fun x y -> x ^^ break1 ^^ break1 ^^ y) l

let string_of_struct str =
  let buf = Buffer.create 16 in
  let doc = Pprint.(^^) (doc_of_struct str) Pprint.hardline in
  Pprint.Buffer.pretty 1.0 Bash.twidth buf doc;
  Buffer.contents buf
