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

(* Don't do this, kids. Works because this functor is applicative. *)
module rec CamlX_: module type of CamlX.Make(Unify.BaseSolver) = CamlX_
open CamlX_
open CamlX
open Unify
open Algebra.Identifiers

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

(* Once all the right variables are in the environment, we simply transcribe a
 * scheme into the right fscheme structure (it's a f_type_term) *)
let type_term_of_uvar env uvar =
  let rec type_term_of_uvar uvar =
    let repr = find uvar in
    match repr.term with
    | None ->
        let fvar = IntMap.find repr.id env.fvar_of_uvar in
        `Var fvar
    | Some (`Cons (head_symbol, cons_args)) ->
        `Cons (head_symbol, List.map type_term_of_uvar cons_args)
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
            env
            rec_flag pat_expr_list
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

      | `Sequence (e1, e2) ->
          `Sequence (translate_expr env e1, translate_expr env e2)

      | `IfThenElse (i, t, e) ->
          `IfThenElse (translate_expr env i, translate_expr env t,
            Option.map (translate_expr env) e)

      | `AssertFalse ->
          `AssertFalse

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
     * stored in the first identifier's pscheme. *)
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
    fun _env upat -> upat

  (* The thing is here, we're only renaming types, and types of top-level
   * bindings are closed, so there's nothing to forward across structure items.
   * This also explains why the environment is fresh for every top-level
   * binding.
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

      | `Type t ->
          let rec debruijnize = function
            | `Var i ->
                `Var (DeBruijn.of_int i)
            | `Cons (head_symbol, args) ->
                `Cons (head_symbol, List.map debruijnize args)
            | `Forall t ->
                `Forall (debruijnize t)
          in
          `Type (object
            method name = t # name
            method arity = t # arity
            method kind = t # kind
            method fields =
              List.map
                (fun (l, ts) -> (l, List.map debruijnize ts))
                (t # fields)
          end)

  in

  List.map (fun x -> translate_struct { fvar_of_uvar = IntMap.empty } x)

module PrettyPrinting = struct
  (* Just generate as many uppercase lambdas as needed *)
  let make lambda n = 
    let open Bash in
    let open Pprint in
    let lambdas = String.concat "" (Jlist.make n (fun _ -> lambda)) in
    let lambdas = color colors.blue "%s" lambdas in
    let lambdas = fancystring lambdas n in
    lambdas

  let gen_lambdas = make "Λ"

  let keyword k =
    let open Pprint in
    let open Bash in
    fancystring (color 208 "%s" k) (String.length k)

  let string_of_type_term t =
    Pprint.string (DeBruijn.string_of_type_term (t: f_type_term :> DeBruijn.type_term))

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
            let scheme = string_of_type_term scheme in
            pdoc ^^ colon ^^ space ^^
            fdoc ^^ lb' ^^ scheme ^^ rb' ^^ space ^^ equals ^^
            space ^^ ldoc ^^
              (nest 2 (break1 ^^ edoc)
            )
          in
          let pat_expr_list = List.map gen pat_expr_list in
          let anddoc = keyword "and" in
          let pat_expr_list = Jlist.concat
            (fun x y -> x ^^ break1 ^^ anddoc ^^ space ^^ y)
            pat_expr_list
          in
          let e2 = doc_of_expr e2 in
          let letdoc = keyword "let" in
          let indoc = keyword "in" in
          let recdoc = if rec_flag then keyword "rec " else empty in
          letdoc ^^ space ^^ recdoc ^^ pat_expr_list ^^ break1 ^^
          indoc ^^ break1 ^^
          e2

      | `Function (type_term, pat_expr_list) ->
          (* type_term of the argument as a whole; it might be a pattern so
           * we have the type of the whole first argument. This is needed for
           * [Desugar] to translate this `Function into a `Fun (`Match...) *)
          let tdoc = string_of_type_term type_term in
          if (List.length pat_expr_list > 1) then
            let gen (pat, expr) =
              let pdoc = doc_of_pat pat in
              let edoc = doc_of_expr expr in
              bar ^^ space ^^ lparen ^^ pdoc ^^ colon ^^ space ^^ tdoc ^^
              rparen ^^ space ^^ minus ^^ rangle ^^ (nest 4 (break1 ^^ edoc))
            in
            let pat_expr_list = List.map gen pat_expr_list in
            let pat_expr_list = Jlist.concat
              (fun x y -> x ^^ hardline ^^ y)
              pat_expr_list
            in
            (keyword "function") ^^ (nest 2 (hardline ^^ pat_expr_list))
          else
            let pat, expr = List.hd pat_expr_list in
            let pdoc = doc_of_pat pat in
            let edoc = doc_of_expr expr in
            (keyword "fun") ^^ space ^^ lparen ^^ pdoc ^^ colon ^^ space ^^
            tdoc ^^ rparen ^^ space ^^ minus ^^ rangle ^^ space ^^ edoc

      | `Instance (ident, instance) ->
          let ident = string (string_of_ident ident) in
          if List.length instance > 0 then
            let instance = List.map (fun x -> string_of_type_term x) instance in
            let instance = Jlist.concat (fun x y -> x ^^ comma ^^ space ^^ y) instance in
            let lb = fancystring (color colors.red "[") 1 in
            let rb = fancystring (color colors.red "]") 1 in
            ident ^^ space ^^ lb ^^ instance ^^ rb
          else
            ident

      | `App (e1, args) ->
          Jlist.concat (fun x y -> x ^^ space ^^ y) (List.map doc_of_expr (e1 :: args))

      | `Match (expr, { young_vars; f_type_term }, pat_expr_list) ->
          let ldoc = gen_lambdas young_vars in
          let lb' = fancystring (color colors.blue "[") 1 in
          let rb' = fancystring (color colors.blue "]") 1 in
          let scheme = string_of_type_term f_type_term in
          let gen (pat, expr) =
            let pdoc = doc_of_pat pat in
            let edoc = doc_of_expr expr in
            bar ^^ space ^^ pdoc ^^ space ^^ minus ^^ rangle ^^
              (nest 4 (break1 ^^ edoc)
            )
          in
          let pat_expr_list = List.map gen pat_expr_list in
          let pat_expr_list = Jlist.concat
            (fun x y -> x ^^ break1 ^^ y)
            pat_expr_list
          in
          let matchdoc = keyword "match" in
          let exprdoc = doc_of_expr expr in
          let withdoc = keyword "with" in
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
          let edoc = Jlist.concat (fun x y -> x ^^ comma ^^ space ^^ y) edocs in
          lparen ^^ edoc ^^ rparen

      | `Const c ->
          doc_of_const c

      | `Construct (c, exprs) ->
          let doc =
            match exprs with
            | [] ->
                empty
            | [x] ->
                space ^^ (doc_of_expr x)
            | xs ->
                space ^^ lparen ^^ (Jlist.concat (fun x y -> x ^^ comma ^^ space ^^
                y) (List.map doc_of_expr xs)) ^^ rparen
          in
          (string c) ^^ doc

      | `AssertFalse ->
          string "assert false"

      | `Sequence (e1, e2) ->
          (doc_of_expr e1) ^^ semi ^^ break1 ^^ (doc_of_expr e2)

      | `IfThenElse (i, t, e) ->
          (keyword "if") ^^ space ^^ (doc_of_expr i) ^^ space ^^ (keyword "then")
          ^^ space ^^ (keyword "begin")
          ^^ (nest 2 (break1 ^^ (doc_of_expr t))) ^^ break1 ^^ (keyword "end") ^^
          begin
            match e with
            | None ->
                empty
            | Some e ->
                (keyword " else begin") ^^
                (nest 2 (break1 ^^ (doc_of_expr e))) ^^ break1 ^^ (keyword
                "end")
          end

      | `Magic t ->
          (string "%magic: ") ^^ (string_of_type_term t)

  and doc_of_pat: f_pattern -> Pprint.document =
    let open Pprint in
    function
      | `Any ->
          underscore

      | `Tuple patterns ->
          let pdocs = List.map doc_of_pat patterns in
          let pdoc = Jlist.concat (fun x y -> x ^^ comma ^^ space ^^ y) pdocs in
          lparen ^^ pdoc ^^ rparen

      | `Or (p1, p2) ->
          let pdoc1 = doc_of_pat p1 in
          let pdoc2 = doc_of_pat p2 in
          pdoc1 ^^ space ^^ bar ^^ space ^^ pdoc2

      | `Construct (c, pats) ->
          let doc =
            match pats with
            | [] ->
                empty
            | [x] ->
                space ^^ (doc_of_pat x)
            | xs ->
                space ^^ lparen ^^ (Jlist.concat (fun x y -> x ^^ comma ^^ space ^^
                y) (List.map doc_of_pat xs)) ^^ rparen
          in
          (string c) ^^ doc


      | `Const c ->
          doc_of_const c

      | `Alias (pat, ident) ->
          lparen ^^ (doc_of_pat pat) ^^ (string " as ") ^^
            (string (string_of_ident ident)) ^^ rparen

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
            let scheme = string_of_type_term scheme in
            pdoc ^^ colon ^^ space ^^
            fdoc ^^ lb' ^^ scheme ^^ rb' ^^ space ^^ equals ^^
            space ^^ ldoc ^^
              (nest 2 (break1 ^^ edoc)
            )
          in
          let pat_expr_list = List.map gen pat_expr_list in
          let anddoc = fancystring (color 208 "and") 3 in
          let pat_expr_list = Jlist.concat
            (fun x y -> x ^^ break1 ^^ anddoc ^^ space ^^ y)
            pat_expr_list
          in
          let letdoc = fancystring (color 208 "let") 3 in
          let recdoc = if rec_flag then (keyword "rec ") else empty in
          letdoc ^^ space ^^ recdoc ^^ pat_expr_list

      | `Type t ->
          let arity = t # arity in
          let args =
            if arity > 0 then
              let int i = string (string_of_int i) in
              let onetwothree =
                let rec build i =
                  if i > 0 then
                    (int i) :: (build (i-1))
                  else
                    [(int 0)]
                in
                List.rev (build arity)
              in
              let args = Jlist.concat (fun x y -> x ^^ comma ^^ space ^^ y) onetwothree in
              let args = if arity > 1 then lparen ^^ args ^^ rparen else args in
              args ^^ space
            else
              empty
          in
          let constructors =
            let build (label, terms) =
              let label = string label in
              let terms =
                match terms with
                | [] ->
                    empty
                | [t] ->
                    (string " of ") ^^ (string_of_type_term t)
                | terms ->
                    let terms =
                      List.map (string_of_type_term) terms
                    in
                    let terms =
                      Jlist.concat (fun x y -> x ^^ space ^^ star ^^ space ^^ y) terms
                    in
                    (string " of ") ^^ terms
              in
              label ^^ terms
            in
            let constructors = List.map build (t # fields) in
            let constructors =
              Jlist.concat (fun x y -> x ^^ space ^^ bar ^^ space ^^ y) constructors
            in
            constructors
          in
          (keyword "type ") ^^ args ^^ (string (t # name)) ^^ space ^^ equals ^^
          space ^^ constructors

    in
    fun str ->
      let l = List.map doc_of_str str in
      Jlist.concat (fun x y -> x ^^ break1 ^^ break1 ^^ y) l

  let string_of_struct str =
    let buf = Buffer.create 16 in
    let doc = Pprint.(^^) (doc_of_struct str) Pprint.hardline in
    Pprint.Buffer.pretty 1.0 Bash.twidth buf doc;
    Buffer.contents buf
end

let string_of_struct = PrettyPrinting.string_of_struct
