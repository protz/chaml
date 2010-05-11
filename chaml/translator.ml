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


type t = f_expression

module DeBruijn = struct
  let lift: int -> f_type_term -> f_type_term =
    fun _ _ -> assert false

  let subst: f_type_term -> type_var -> f_type_term =
    fun _ _ -> assert false
end

module IntMap = Jmap.Make(struct
  type t = int
  let compare = compare
end)

(* Various helpers to work with environments *)

type env = {
  fvar_of_uvar: type_var IntMap.t;
}

let lift_add env uvar =
  let new_map =
    IntMap.map (fun x -> { index = x.index + 1 }) env.fvar_of_uvar
  in
  let new_map =
    IntMap.add (UnionFind.find uvar).id { index = 0 } new_map
  in
  Error.debug "[TLiftAdd] Adding %a\n" uvar_name uvar;
  { fvar_of_uvar = new_map }

let union { fvar_of_uvar = map1 } { fvar_of_uvar = map2 } =
  { fvar_of_uvar = IntMap.union map1 map2 }

(* The core functions *)

(* Once all the right variables are in the environment, we simply transcribe a
 * scheme into the right fscheme structure (it's a f_type_term) *)
let type_term_of_uvar env uvar =
  let rec type_term_of_uvar uvar =
    let repr = UnionFind.find uvar in
    match repr.term with
    | None ->
        let fvar = IntMap.find repr.id env.fvar_of_uvar in
        `Var fvar
    | Some (`Cons (cons_name, cons_args)) ->
        `Cons (cons_name, List.map type_term_of_uvar cons_args)
  in
  type_term_of_uvar uvar 

let translate =
  let rec translate_expr: env -> CamlX.Make(BaseSolver).expression -> f_expression = 
    fun env uexpr ->
    match uexpr with
      | `Let (pat_expr_list, e2) ->
          let pat_expr_list =
            List.map
              (fun (upat, pscheme, uexpr) ->
                (* The patterns are translated in the current environment *)
                let fpat = translate_pat env ~assign_schemes:false upat in
                let fcoerc = translate_coerc env fpat pscheme in 
                (* Then we move to the rigt of let p1 = e1, this is where we
                 * introduce the new type variables *)
                let new_env = List.fold_left lift_add env pscheme.p_young_vars in
                Error.debug
                  "[TScheme] %d variables in this pattern\n"
                  (List.length pscheme.p_young_vars);
                let fexpr = translate_expr new_env uexpr in
                (fpat, fcoerc, (List.length pscheme.p_young_vars), fexpr)
              )
              pat_expr_list
          in
          let fexpr = translate_expr env e2 in
          `Let (pat_expr_list, fexpr)

      | `Lambda pat_expr_list ->
           let pat_expr_list = List.map
            (fun (upat, uexpr) ->
              let fpat = translate_pat env ~assign_schemes:true upat in
              let fexpr = translate_expr env uexpr in
              fpat, fexpr
            )
            pat_expr_list
          in
          `Lambda pat_expr_list

      | `Instance (ident, instance) ->
          let instance =
            List.map
              (fun x -> IntMap.find (UnionFind.find x).id env.fvar_of_uvar)
              !instance
          in
          `Instance (ident, instance)

      | `App (e1, args) ->
          `App (translate_expr env e1, List.map (translate_expr env) args)

      | `Match (_e1, _pat_expr_list) ->
          failwith "Match not implemented"

      | `Tuple (exprs) ->
          `Tuple (List.map (translate_expr env) exprs)

      | `Const _ as r ->
          r

  (* [translate_pat] just generates patterns as needed. It doesn't try to
   * assign schemes to variables if those are on the left-hand side of a pattern. *)
  and translate_pat: env -> assign_schemes:bool -> CamlX.Make(BaseSolver).pattern -> f_pattern =
    fun env ~assign_schemes upat ->
    match upat with
      | `Any as r ->
          r

      | `Tuple patterns ->
          `Tuple (List.map (translate_pat env ~assign_schemes) patterns)

      | `Or (p1, p2) ->
          `Or (translate_pat env ~assign_schemes p1, translate_pat env ~assign_schemes p2)

      | `Var (ident, { scheme_var = scheme }) ->
          let scheme =
            if assign_schemes then
              Some (type_term_of_uvar env scheme)
            else
              None
          in
          `Var (ident, scheme)

  (* [translate_coercion] walks down the pattern scheme and the pattern in
   * parallel, and returns a list of coercions needed to properly type this
   * pattern *)
  and translate_coerc: env -> f_pattern -> unifier_pscheme -> f_coercion =
    fun env pat { p_uvar = uvar; p_young_vars = young_vars } ->
      let type_cons_tuple i =
        let fake_list = Jlist.make i () in
        let `Cons (cons_name, _) = Algebra.TypeCons.type_cons_tuple fake_list in
        cons_name
      in
      let repr = UnionFind.find uvar in
      match pat, repr with
      | `Tuple patterns, { term = Some (`Cons (cons_name, cons_args)) }
        when cons_name = type_cons_tuple (List.length patterns) ->
          (* Let's move all the variables inside the branches *)
          let gen pat uvar =
            translate_coerc env pat { p_uvar = uvar; p_young_vars = young_vars }
          in
          (* We have the first coercion *)
          let c = `TupleCovariant (List.map2 gen patterns cons_args) in
          (* Explain that we inject all the variables inside the branches *)
          List.fold_right (fun _ c -> `ForallInTuple c) young_vars c
      | _ ->
          `Identity
  in

  translate_expr { fvar_of_uvar = IntMap.empty }

let concat f l =
  List.fold_left f (List.hd l) (List.tl l)

let string_of_type_term scheme =
  let open TypePrinter in
  let scheme =
    (scheme: f_type_term :> type_var inspected_var)
  in
  let scheme = string_of_type
    ~string_of_key:(`Custom (fun x -> string_of_int x.index))
    scheme
  in
  scheme

(* Just generate as many uppercase lambdas as needed *)
let gen_lambdas n = 
  let lambda = "Λ" in
  let lambdas = String.concat "" (Jlist.make n lambda) in
  let lambdas = Bash.color Bash.colors.Bash.blue "%s" lambdas in
  let lambdas = Pprint.fancystring lambdas n in
  lambdas

(* Pretty-printing stuff *)
let rec doc_of_expr: f_expression -> Pprint.document = 
  let open Pprint in
  function
    | `Let (pat_expr_list, e2) ->
        let gen (pat, coercion, nlambdas, expr) =
          let open Bash in
          let pdoc = doc_of_pat pat in
          let edoc = doc_of_expr expr in
          let cdoc = doc_of_coerc coercion in
          let lb = string (color colors.green "[") in
          let rb = string (color colors.green "]") in
          let ldoc = gen_lambdas nlambdas in
          pdoc ^^ space ^^ equals ^^ space ^^
          lb ^^ cdoc ^^ rb ^^ space
          ^^ ldoc ^^ dot ^^
          (nest 2 (break1 ^^ edoc))
        in
        let pat_expr_list = List.map gen pat_expr_list in
        let pat_expr_list = concat
          (fun x y -> x ^^ break1 ^^ (string "and") ^^ y)
          pat_expr_list
        in
        let e2 = doc_of_expr e2 in
        let letdoc = fancystring (Bash.color 208 "let") 3 in
        let indoc = fancystring (Bash.color 208 "in") 2 in
        letdoc ^^ space ^^ pat_expr_list ^^ break1 ^^
        indoc ^^ break1 ^^
        e2

    | `Lambda pat_expr_list ->
        if (List.length pat_expr_list > 1) then
          let gen (pat, expr) =
            let pdoc = doc_of_pat pat in
            let edoc = doc_of_expr expr in
            bar ^^ space ^^ pdoc ^^ space ^^ minus ^^ rangle ^^ (nest 4 (break1 ^^ edoc))
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
          (string "fun") ^^ space ^^ pdoc ^^ space ^^ minus ^^ rangle ^^ space ^^ edoc

    | `Instance (ident, _instance) ->
        string (string_of_ident ident)

    | `App (e1, args) ->
        concat (fun x y -> x ^^ space ^^ y) (List.map doc_of_expr (e1 :: args))

    | `Match (_e1, _pat_expr_list) ->
        failwith "Match pretty-printing not implemented"

    | `Tuple (exprs) ->
        (* XXX compute operator priorities cleanly here *)
        let paren_if_needed = function
          | `Lambda _ as l ->
              lparen ^^ (doc_of_expr l) ^^ rparen
          | x ->
              doc_of_expr x
        in
        let edocs = List.map paren_if_needed exprs in
        let edoc = concat (fun x y -> x ^^ comma ^^ space ^^ y) edocs in
        lparen ^^ edoc ^^ rparen

    | `Const c ->
        doc_of_const c

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

    | `Var (ident, (scheme: f_type_term option)) ->
        match scheme with
        | None ->
            string (string_of_ident ident)
        | Some scheme ->
            let scheme = string_of_type_term scheme in
            let scheme = fancystring
              (Bash.color Bash.colors.Bash.red "%s" scheme)
              (String.length scheme)
            in
            lparen ^^ (string (string_of_ident ident)) ^^ colon ^^ space
            ^^ scheme ^^ rparen

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
        string s
    | `Unit ->
        string "()"

and doc_of_coerc: f_coercion -> Pprint.document =
  let open Pprint in
  function
    | `ForallInTuple c ->
        let doc = doc_of_coerc c in
        lparen ^^ (fancystring "∀/x" 3) ^^ rparen ^^ semi ^^ space ^^ doc

    | `ForallElim (_c, _t) ->
        failwith "Not implemented: `ForallElim\n"

    | `TupleCovariant coercions ->
        let coercions = List.map doc_of_coerc coercions in
        let coercions = concat (fun x y -> x ^^ comma ^^ space ^^ y) coercions in
        lparen ^^ star ^^ rparen ^^ lbracket ^^ coercions ^^ rbracket
        ^^ semi ^^ space

    | `ForallIntro c ->
        let doc = doc_of_coerc c in
        lparen ^^ (fancystring "∀intro;" 6) ^^ rparen ^^ semi ^^ space ^^ doc

    | `Identity ->
        empty

let string_of_t expr =
  let buf = Buffer.create 16 in
  let doc = Pprint.(^^) (doc_of_expr expr) Pprint.hardline in
  Pprint.Buffer.pretty 1.0 Bash.twidth buf doc;
  Buffer.contents buf
