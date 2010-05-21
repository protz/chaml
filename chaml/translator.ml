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

let concat f l =
  List.fold_left f (List.hd l) (List.tl l)

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

(* The core functions *)

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
                (* When generating the coercion, we have the invariant that
                 * variables are sorted according to the global order. That's
                 * important for \forall elimination. *)
                let fcoerc = translate_coerc env fpat pscheme in 
                let young_vars = List.length pscheme.p_young_vars in
                Error.debug "[TScheme] %d variables in this pattern\n" young_vars;
                (* Then we move to the rigt of let p1 = e1, this is where we
                 * introduce the new type variables *)
                let new_env = List.fold_left lift_add env pscheme.p_young_vars in
                let scheme = type_term_of_uvar new_env pscheme.p_uvar in
                let clblock = {
                  coercion = fcoerc;
                  young_vars;
                  type_term = scheme;
                } in
                let fexpr = translate_expr new_env uexpr in
                (fpat, clblock, fexpr)
              )
              pat_expr_list
          in
          let fexpr = translate_expr env e2 in
          `Let (pat_expr_list, fexpr)

      | `Function (pscheme, pat_expr_list) ->
           let pat_expr_list = List.map
            (fun (upat, uexpr) ->
              let fpat = translate_pat env ~assign_schemes:true upat in
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

      | `Match (_e1, _pscheme, _pat_expr_list) ->
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
          let gen i pat uvar =
            let c =
              translate_coerc env pat { p_uvar = uvar; p_young_vars = young_vars }
            in
            `CovarTuple (i, c)
          in
          (* We have the first coercion *)
          let c =
            concat (fun x y -> `Compose (x, y)) (Jlist.map2i gen patterns cons_args)
          in
          (* Explain that we inject all the variables inside the branches *)
          let rec fold uvars =
            match uvars with
            | [] ->
                `Compose (`DistribTuple, `Id)
            | _ :: tl ->
                let c = fold tl in
                let c1 = `ForallIntroC (
                  `Compose (`ForallElim (`Var { index = 0 }), c))
                in
                `Compose (c1, `DistribTuple)
          in
          `Compose (fold young_vars, c)

      | `Var (_, None), _ ->
          (* Are we still under \Lambdas? If not, then we've got a proper
           * coercion. If we still have some \Lambdas, we must remove those that
           * are useless. *)
          if List.length young_vars = 0 then
            `Id
          else
            (* XXX this probably has a bad complexity *)
            let seen = Uhashtbl.create 16 in
            (* Mark all the variables quantified in this scheme *)
            let rec walk uvar =
              let repr = UnionFind.find uvar in
              if not (Uhashtbl.mem seen repr) then begin
                Uhashtbl.add seen repr ();
                match repr.term with
                  | None ->
                      ()
                  | Some (`Cons (_cons_name, cons_args)) ->
                      List.iter walk cons_args
              end
            in
            walk uvar;
            (* Create the vector for elimination.
             * None = leave as is, Some x = instanciate with x *)
            let rec fold uvars =
              match uvars with
              | [] -> `Id
              | uvar :: tl ->
                 let repr = UnionFind.find uvar in
                 if not (Uhashtbl.mem seen repr) then
                   `Compose (`ForallElim Algebra.TypeCons.type_cons_bottom, fold tl)
                 else
                   match fold tl with
                   | `Id -> `Id (* Don't uselessy rebind *)
                   | c ->
                       `ForallIntroC (
                         `Compose (`ForallElim (`Var { index = 0 }), c)
                       )
            in
            fold young_vars
                    
      | _ ->
          failwith "Only supporting coercions for tuples at the moment\n"
  in

  translate_expr { fvar_of_uvar = IntMap.empty }

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
  let open Bash in
  let open Pprint in
  let lambda = "Λ" in
  let lambdas = String.concat "" (Jlist.make n lambda) in
  let lambdas = color colors.blue "%s" lambdas in
  let lambdas = fancystring lambdas n in
  lambdas

(* Pretty-printing stuff *)
let rec doc_of_expr: f_expression -> Pprint.document = 
  let open Pprint in
  let open Bash in
  function
    | `Let (pat_expr_list, e2) ->
        let gen (pat, { coercion; young_vars = nlambdas; type_term = scheme }, expr) =
          let pdoc = doc_of_pat pat in
          let edoc = doc_of_expr expr in
          let cdoc = doc_of_coerc coercion in
          let lb = fancystring (color colors.green "▸ [") 3 in
          let rb = fancystring (color colors.green "]") 1 in
          let lb' = fancystring (color colors.blue "[") 1 in
          let rb' = fancystring (color colors.blue "]") 1 in
          let ldoc = gen_lambdas nlambdas in
          let scheme = string (string_of_type_term scheme) in
          pdoc ^^ space ^^ equals ^^ (nest 2 (break1 ^^
          ldoc ^^ space ^^ lb' ^^ scheme ^^ rb' ^^ dot)) ^^
          (nest 2 (break1 ^^ edoc ^^
            break1 ^^ lb ^^ cdoc ^^ rb))
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
        letdoc ^^ space ^^ pat_expr_list ^^ break1 ^^
        indoc ^^ break1 ^^
        e2

    | `Function (_type_term, pat_expr_list) ->
        (* type_term of the argument as a whole; it might be a pattern so
         * we have the type of the whole first argument. This is needed for
         * [Desugar] to translate this `Function into a `Fun (`Match...) *)
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

    | `Instance (ident, instance) ->
        let ident = string (string_of_ident ident) in
        if List.length instance > 0 then
          let instance = List.map (fun x -> string (string_of_type_term x)) instance in
          let instance = concat (fun x y -> x ^^ comma ^^ space ^^ y) instance in
          let lb = fancystring (color colors.red "[") 1 in
          let rb = fancystring (color colors.red "]") 1 in
          ident ^^ space ^^ lb ^^ instance ^^ rb
        else
          ident

    | `App (e1, args) ->
        concat (fun x y -> x ^^ space ^^ y) (List.map doc_of_expr (e1 :: args))

    | `Match (_e1, _pscheme, _pat_expr_list) ->
        failwith "Match pretty-printing not implemented"

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
        dquote ^^ (string s) ^^ dquote
    | `Unit ->
        string "()"

and doc_of_coerc: f_coercion -> Pprint.document =
  let open Pprint in
  function
    | `Id ->
        string "id"

    | `Compose (c1, c2) ->
       let c1 = doc_of_coerc c1 in
       let c2 = doc_of_coerc c2 in
       c1 ^^ semi ^^ space ^^ c2

    | `ForallIntro ->
        lparen ^^ (fancystring "∀" 1) ^^ rparen

    | `ForallIntroC c ->
        let c = doc_of_coerc c in
        (fancystring "∀" 1) ^^ lbracket ^^ c ^^ rbracket

    | `ForallElim arg ->
        let arg = string (string_of_type_term arg) in
        (fancystring "•" 1) ^^ lbracket ^^ arg ^^ rbracket 

    | `CovarTuple (i, coercion) ->
        let coercion = doc_of_coerc coercion in
        let i = string (string_of_int i) in
        (string "p") ^^ lbracket ^^ i ^^ rbracket ^^ lbracket ^^ coercion ^^ rbracket

    | `DistribTuple ->
        fancystring "∀→" 2

let string_of_expr expr =
  let buf = Buffer.create 16 in
  let doc = Pprint.(^^) (doc_of_expr expr) Pprint.hardline in
  Pprint.Buffer.pretty 1.0 Bash.twidth buf doc;
  Buffer.contents buf
