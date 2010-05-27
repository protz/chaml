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
open CamlX

type env = {
  atom_of_ident: Atom.t IdentMap.t;
}

type cenv = {
  forall: int;
  type_term: DeBruijn.type_term;
  pattern: Core.pattern;
}

(* Introduce new identifiers in scope, possibly overriding previously defined
 * ones. *)
let introduce: Atom.t list -> env -> env =
  fun atoms { atom_of_ident } ->
    let atom_of_ident = List.fold_left
      (fun map atom ->
        IdentMap.add (Atom.ident atom) atom map)
      atom_of_ident
      atoms
    in
    { atom_of_ident }

let find: ident -> env -> Atom.t =
  fun ident { atom_of_ident } ->
    IdentMap.find ident atom_of_ident

let concat f l =
  List.fold_left f (List.hd l) (List.tl l)

let rec desugar_expr: env -> CamlX.f_expression -> Core.expression =
  fun env expr ->
  match expr with
  | `Let (pat_coerc_exprs, e2) ->
      (* We have the invariant that all identifiers are distinct, we explicitely
       * checked for that in the constraint generator. This is the first pass
       * that allows us to get a pointer to all generated atoms and patterns. *)
      let new_patterns, new_atoms =
        List.split
          (List.map (fun (pat, _, _) -> desugar_pat env pat) pat_coerc_exprs)
      in
      (* We generate e2 with all identifiers in scope *)
      let new_env = introduce (List.flatten new_atoms) env in
      let e2 = desugar_expr new_env e2 in
      (* And then we desugar all of the initial branches in the same previous
       * scope *)
      let gen_branch e2 (_, { young_vars; f_type_term = type_term }, e1) pat = 
        let e1 = desugar_expr env e1 in
        (* Beware, now we must generate proper F terms *)
        let rec add_lambda i e =
          if i > 0 then
            add_lambda (i - 1) (`TyAbs e)
          else
            e
        in
        (* So we generate proper Lambdas *)
        let e1 = add_lambda young_vars e1 in
        (* Generate the coercion *)
        let new_pat =
          generate_coerc new_env { pattern = pat; forall = young_vars; type_term }
        in
        (* The pattern has already been translated in a first pass. Now check if
         * it's just an identifier (we can use a regular let-binding) or a
         * pattern (then, we use a match) *)
        match pat with
        | `Var atom ->
            Error.debug "[DLet] Found a regular let\n";
            `Let (`Var atom, e1, e2)
        | _ ->
            `Match (e1, [(new_pat, e2)])
      in
      (* Wrap everyone around e2 *)
      let expr = List.fold_left2 gen_branch e2 pat_coerc_exprs new_patterns in
      expr

  | `Instance (ident, type_terms) ->
      (* Remember, we have the invariant that the instance variables are in the
       * global order, and so are the scheme variables (fingers crossed)! *)
      let app expr type_term =
        `TyApp (expr, type_term)
      in
      let instance = `Instance (find ident env) in
      List.fold_left app instance type_terms

  | `App (expr, exprs) ->
      let exprs = expr :: exprs in
      let exprs = List.map (desugar_expr env) exprs in
      `App (List.hd exprs, List.tl exprs)

  | `Function (arg_type, pat_exprs) ->
      begin match pat_exprs with
          (* We deal with the trivial case fun x -> where x is already an identifier *)
          | [(`Var _ as v, expr)] ->
              begin match desugar_pat env v with
              | (`Var _ as v), ([_] as atoms) ->
                  let new_env = introduce atoms env in
                  `Fun (v, arg_type, desugar_expr new_env expr)
              | _ ->
                  assert false
              end

          (* This is the general case. We either have many branches, or a
           * pattern instead of a single var. *)
          | _ ->
            (* First create a fake ident. We don't care about unique names anymore,
             * because atoms have a uniquely generated identifier. *)
            let atom = Atom.fresh (ident "__internal" Location.none) in
            (* Now function is forbidden, only fun x -> with x being a single
             * var. This is where the type of the whole argument turns out to be
             * useful, and this is why we've been forwarding it through the many
             * passes since the beginning. *)
            let var = `Var atom in
            (* Take an instance of the introduced variable. Because we're in ML,
             * there's no universal quantification on the type of x so there's no type
             * variables to instanciate, so no `TyApp. *)
            let instance = `Instance atom in
            (* Translate the expressions and the patterns *)
            let gen (pat, expr) =
              let pat, atoms = desugar_pat env pat in
              let new_env = introduce atoms env in
              let expr = desugar_expr new_env expr in
              (pat, expr)
            in
            (* Finally return fun x -> match x with [...] *)
            let mmatch = `Match (instance, (List.map gen pat_exprs)) in
            `Fun (var, arg_type, mmatch)
      end

  | `Match (_expr, _clblock, _forall, _pat_exprs) ->
      failwith "Match not implemented"

  | `Tuple exprs ->
      let exprs = List.map (desugar_expr env) exprs in
      `Tuple exprs

  | `Const c ->
      let c = desugar_const c in
      `Const c

and desugar_pat env ?rebind pat =
  match pat with
  | `Var (ident, _typ) ->
      if Option.unit_bool rebind then
        `Var (find ident env), []
      else
        let atom = Atom.fresh ident in
        `Var atom, [atom]

  | `Tuple patterns ->
      let patterns, atoms = List.split (List.map (desugar_pat ?rebind env) patterns) in
      `Tuple patterns, List.flatten atoms

  | `Or (p1, p2) ->
      (* We must ensure we bind exactly the same identifiers here. This works
       * because we checked previously that the set of identifiers is the same
       * in both branches (in the constraint generation). So we are sure that
       * all the indentifiers we lookup are exactly the ones we just added in
       * premad_env. *)
      Error.debug "[DOr] Orpat in\n";
      let p1, a1 = desugar_pat ?rebind env p1 in
      let premade_env = introduce a1 env in
      let p2, a2 = desugar_pat premade_env ~rebind:() p2 in
      assert (List.length a2 = 0);
      Error.debug "[DOr] Orpat out\n";
      `Or (p1, p2), a1

  | `Any ->
      `Any, []

(* [generate_coercion] walks down the pattern scheme and the pattern in
 * parallel, and returns a list of coercions needed to properly type this
 * pattern *)
and generate_coerc env cenv =
  let type_cons_tuple i =
    let fake_list = Jlist.make i () in
    let `Cons (cons_name, _) = Algebra.TypeCons.type_cons_tuple fake_list in
    cons_name
  in
  let compose c1 c2 =
    match c1, c2 with
    | `Id, c1 -> c1
    | c2, `Id -> c2
    | _ -> `Compose (c1, c2)
  in 
  (* Instead of returning a pattern every time and possibly using
   *  `Coerce (`Coerce ( ... ) ... )
   * we choose to accumulate coercions and compose the pattern with the coercion
   * only at the last moment, i.e. when the function below returns, or when we
   * encounter a `Or pattern. *)
  let rec generate_coerc env { forall; type_term; pattern } =
    match pattern, type_term with
    | `Tuple patterns, `Cons (cons_name, cons_args)
      when cons_name = type_cons_tuple (List.length patterns) ->
        (* Let's move all the variables inside the branches *)
        let gen i pattern type_term =
          let pattern, c =
            generate_coerc env { forall; pattern; type_term; }
          in
          pattern, if c = `Id then `Id else `CovarTuple (i, c)
        in
        (* We have the first coercion *)
        let patterns, coercions = List.split (Jlist.map2i gen patterns cons_args) in
        let c = concat compose coercions in
        (* Explain that we inject all the variables inside the branches *)
        let rec fold forall =
          if forall = 0 then
              `Id
          else
            let c = fold (forall - 1) in
            let c1 = if c = `Id then `Id else `ForallCovar c in
            compose c1 `DistribTuple
        in
        `Tuple patterns, `Compose (fold forall, c)

    | `Var _, _ ->
        (* Are we still under \Lambdas? If not, then we've got a proper
         * coercion. If we still have some \Lambdas, we must remove those that
         * are useless. *)
        if forall = 0 then
          pattern, `Id
        else
          (* Mark all the variables quantified in this scheme
             XXX this probably has a bad complexity *)
          let seen = Array.make forall false in
          let rec walk type_term =
            match type_term with
              | `Var v ->
                  let i = DeBruijn.index v in
                  if i < forall then
                    seen.(DeBruijn.index v) <- true
              | `Cons (_cons_name, cons_args) ->
                  List.iter walk cons_args
          in
          walk type_term;
          (* We remove quantifiers we don't use *)
          let rec fold i =
            if i = 0 then
              `Id
            else
               let c = fold (i - 1) in
               if not seen.(i-1) then
                 let celim = `ForallElim Algebra.TypeCons.type_cons_bottom in
                 compose celim c
               else
                 if c = `Id then `Id else `ForallCovar c
          in
          pattern, fold forall

    | `Or (p1, p2), _ ->
        let p1, c1 = generate_coerc env { forall; type_term; pattern = p1 } in
        let p2, c2 = generate_coerc env { forall; type_term; pattern = p2 } in
        let p1 = if c1 = `Id then p1 else `Coerce (p1, c1) in
        let p2 = if c2 = `Id then p2 else `Coerce (p2, c2) in
        `Or (p1, p2), `Id

    | `Any, _ ->
        `Any, `Id
                  
    | _ ->
        failwith "Only supporting coercions for tuples at the moment\n"
  in
  let pat, coerc = generate_coerc env cenv in
  if coerc = `Id then pat else `Coerce (pat, coerc)

and desugar_const const =
  match const with
  | `Float f ->
      let f = float_of_string f in
      `Float f
  | `Char _ | `Int _ | `String _ | `Unit as x ->
      x

let desugar expr =
  let env = { atom_of_ident = IdentMap.empty } in
  desugar_expr env expr


(* Pretty-printing stuff *)

let pcolor ?l c s =
  let l = Option.map_none (String.length s) l in
  Pprint.fancystring (Bash.color c "%s" s) l

let arrow = pcolor Bash.colors.Bash.yellow "->"

let rec doc_of_expr: Core.expression -> Pprint.document = 
  let open Pprint in
  let open Bash in
  function
    | `TyAbs e ->
        let edoc = doc_of_expr e in
        let lambda = pcolor colors.blue ~l:1 "Λ" in
        begin match e with
        | `TyAbs _ ->
            lambda ^^ edoc
        | _ ->
            lambda ^^ dot ^^ space ^^ edoc
        end

    | `TyApp (e, t) ->
        let edoc = doc_of_expr e in
        let t = string (DeBruijn.string_of_type_term t) in
        let bullet = pcolor colors.red ~l:1 "•" in
        let lb = pcolor colors.red "[" in
        let rb = pcolor colors.red "]" in
        edoc ^^ bullet ^^ lb ^^ t ^^ rb

    | `Let (`Var v, e1, e2) ->
        let letdoc = pcolor colors.yellow "let" in
        let vdoc = string (Atom.string_of_atom v) in
        let indoc = pcolor colors.yellow "in" in
        let e1 = doc_of_expr e1 in
        let e2 = doc_of_expr e2 in
        letdoc ^^ space ^^ vdoc ^^ space ^^ equals ^^ 
          (nest 2 (break1 ^^ e1)) ^^
        break1 ^^ indoc ^^ break1 ^^
        e2

    | `Fun (`Var v, t, e2) ->
        let vdoc = string (Atom.string_of_atom v) in
        let t = string (DeBruijn.string_of_type_term t) in
        let vdoc = lparen ^^ vdoc ^^ colon ^^ space ^^ t ^^ rparen in
        let e2 = doc_of_expr e2 in
        let edoc = nest 2 (break1 ^^ e2) in
        (pcolor 207 ~l:1 "λ") ^^ space ^^ vdoc ^^ space ^^ arrow ^^ space ^^ edoc

    | `Instance atom ->
        string (Atom.string_of_atom atom)

    | `App (e1, args) ->
        concat (fun x y -> x ^^ space ^^ y) (List.map doc_of_expr (e1 :: args))

    | `Match (e, pat_exprs) ->
        let edoc = doc_of_expr e in
        let bar = pcolor colors.yellow "|" in
        let rec gen_split pat =
          match pat with
          | `Or (p1, p2) ->
              (gen_split p1) ^^ break1 ^^ bar ^^ space ^^ (gen_split p2)
          | _ ->
              doc_of_pat pat
        in
        let gen (pat, expr) =
          let pdoc = gen_split pat in
          let edoc = doc_of_expr expr in
          bar ^^ space ^^ pdoc ^^ space ^^ arrow ^^
            (nest 4 (break1 ^^ edoc))
        in
        let pat_exprs = List.map gen pat_exprs in
        let pat_exprs = concat (fun x y -> x ^^ break1 ^^ y) pat_exprs in
        let matchdoc = pcolor colors.yellow "match" in
        let withdoc = pcolor colors.yellow "with" in
        matchdoc ^^
          (nest 2 (break1 ^^ edoc)) ^^ break1 ^^ withdoc ^^
        (nest 2 (break1 ^^ pat_exprs))

    | `Tuple (exprs) ->
        (* XXX compute operator priorities cleanly here *)
        let has_fun = List.exists (function `Fun _ -> true | _ -> false) exprs in
        let may_break = if has_fun then (fun x -> nest 2 (break1 ^^ x)) else fun x -> x in
        let paren_if_needed = function
          | `Fun _ as l ->
              nest 2 (break1 ^^ lparen ^^ (doc_of_expr l) ^^ rparen)
          | x ->
              may_break (doc_of_expr x)
        in
        let edocs = List.map paren_if_needed exprs in
        let edoc = concat (fun x y -> x ^^ comma ^^ space ^^ y) edocs in
        lparen ^^ edoc ^^ rparen

    | `Const c ->
        doc_of_const c

and doc_of_pat: Core.pattern -> Pprint.document =
  let open Pprint in
  let open Bash in
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

    | `Var atom ->
        string (Atom.string_of_atom atom)

    | `Coerce (pat, coerc) ->
        let pdoc = doc_of_pat pat in
        let cdoc = doc_of_coerc coerc in
        let triangle = pcolor colors.green ~l:1 "▸" in
        pdoc ^^ space ^^ triangle ^^ space ^^ cdoc

and doc_of_const: Core.const -> Pprint.document =
  let open Pprint in
  function
    | `Char c ->
        squote ^^ (char c) ^^ squote
    | `Int i ->
        string (string_of_int i)
    | `Float f ->
        string (string_of_float f)
    | `String s ->
        dquote ^^ (string s) ^^ dquote
    | `Unit ->
        string "()"

and doc_of_coerc: Core.coercion -> Pprint.document =
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

    | `ForallCovar c ->
        let c = doc_of_coerc c in
        (fancystring "∀co" 3) ^^ lbracket ^^ c ^^ rbracket

    | `ForallElim arg ->
        let arg = string (DeBruijn.string_of_type_term arg) in
        (fancystring "•" 1) ^^ lbracket ^^ arg ^^ rbracket 

    | `CovarTuple (i, coercion) ->
        let coercion = doc_of_coerc coercion in
        let i = string (string_of_int i) in
        (string "p") ^^ i ^^ lbracket ^^ coercion ^^ rbracket

    | `DistribTuple ->
        fancystring "∀→" 2

let string_of_expr expr =
  let buf = Buffer.create 16 in
  let doc = Pprint.(^^) (doc_of_expr expr) Pprint.hardline in
  Pprint.Buffer.pretty 1.0 Bash.twidth buf doc;
  Buffer.contents buf
