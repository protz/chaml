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
open Algebra.Core
open Algebra.TypeCons
open CamlX
open Core
open DeBruijn
module AtomMap = Jmap.Make(Atom)
module StringMap = Jmap.Make(String)

(* We have environments, and a bunch of helpers to deal with them *)
type env = {
  atom_of_ident: Atom.t IdentMap.t;
  atom_of_type: Atom.t StringMap.t;
  rec_atoms: int AtomMap.t;
}

let introduce: Atom.t list -> env -> env =
  fun atoms -> function { atom_of_ident; _ } as env ->
    let atom_of_ident = List.fold_left
      (fun map atom ->
        IdentMap.add (Atom.ident atom) atom map)
      atom_of_ident
      atoms
    in
    { env with atom_of_ident }

let enter_letrec: env -> Atom.t list -> int -> env =
  function { rec_atoms; _ } as env -> fun atoms i ->
    let rec_atoms = List.fold_left
      (fun map atom ->
        AtomMap.add atom i map)
      rec_atoms
      atoms
    in
    { env with rec_atoms }

let register_user_type
    (env: env)
    (name: string)
    (atom: Atom.t)
    : env =
  let atom_of_type = StringMap.add name atom env.atom_of_type in
  { env with atom_of_type }

let find: ident -> env -> Atom.t =
  fun ident { atom_of_ident; _ } ->
    IdentMap.find ident atom_of_ident

(* Quick helpers for manipulating types and terms. We need to wrap terms and
 * types with Lambdas and forall according to the information we have in the AST. *)
let rec wrap_lambda i e =
  if i > 0 then
    wrap_lambda (i - 1) (`TyAbs e)
  else
    e

let rec wrap_forall i t =
  if i = 0 then
    t
  else
    `Forall (wrap_forall (i - 1) t)

let strip_forall =
  let rec strip i =
    function
    | `Forall t ->
        strip (i+1) t
    | t ->
        (i, t)
  in
  strip 0

let rec desugar_expr
        (env: env)
        (expr: CamlX.f_expression)
        : expression =
  match expr with
  | `Let (rec_flag, pat_coerc_exprs, e2) ->
      if rec_flag then
        let new_env, var_type_exprs = desugar_letrec env pat_coerc_exprs in
        let e2 = desugar_expr new_env e2 in
        (* We explicitely forbid anything but identifiers in the LHS of a
         * let-rec. This is enforced in the constraint generator, so we're
         * confident we have either a variable or a coerced variable in this
         * pattern *)
        let e2, var_type_exprs = List.fold_left
          (fun (acc, var_type_exprs) (pat, typ, expr) ->
            match pat with
            | `Coerce (`Var _ as var, _) ->
                `Match (`Instance var, [pat, acc]),
                (var, typ, expr) :: var_type_exprs
            | `Var _ as var ->
                acc,
                (var, typ, expr) :: var_type_exprs
            | _ ->
                assert false
          )
          (e2, [])
          var_type_exprs
        in
        `LetRec (List.rev var_type_exprs, e2)
      else
        (* We have the invariant that all identifiers are distinct, we explicitely
         * checked for that in the constraint generator. This is the first pass
         * that allows us to get a pointer to all generated atoms and patterns. *)
        let new_patterns, new_atoms =
          List.split
            (List.map (fun (pat, _, _) -> desugar_pat env pat) pat_coerc_exprs)
        in
        (* We desugar all branches in the initial scope *)
        let gen_branch e2 (_, { young_vars; f_type_term = type_term }, e1) pat =
          let e1 = desugar_expr env e1 in
          (* Beware, now we must generate proper F terms. Don't forget to add Lambdas. *)
          let e1 = wrap_lambda young_vars e1 in
          (* Generate the coercion *)
          let type_term = desugar_type env type_term in
          let type_term = wrap_forall young_vars type_term in
          let pat = add_coercions_to_pattern env pat type_term in
          (* The pattern has already been translated in a first pass. Now check if
           * it's just an identifier (we can use a regular let-binding) or a
           * pattern (then, we use a match). This is optional, but gives cleaner asts. *)
          match pat with
          | `Var atom ->
              Error.debug "[DLet] Found a regular let\n";
              `Let (`Var atom, e1, e2)
          | `Any ->
              Error.debug "[DAny] Let's not use match for that one\n";
              `Let (`Var (Atom.fresh (ident "_" Location.none)), e1, e2)
          | _ ->
              `Match (e1, [pat, e2])
        in
        (* We generate e2 with all identifiers in scope *)
        let new_env = introduce (List.flatten new_atoms) env in
        let e2 = desugar_expr new_env e2 in
        (* Wrap everyone around e2 *)
        let expr = List.fold_left2 gen_branch e2 pat_coerc_exprs new_patterns in
        expr

  | `Instance (ident, type_terms) ->
      (* Remember, we have the invariant that the instance variables are in the
       * global order, and so are the scheme variables (fingers crossed)! *)
      let app expr type_term =
        let type_term = desugar_type env type_term in
        `TyApp (expr, type_term)
      in
      let atom = find ident env in
      (* This is a trick that allows us to transform ML-style recursion (no
       * re-instanciation) into regular F-style recursion (identifiers are
       * given a polymorphic type and are reinstanciated in the recursive
       * definitions. *)
      let type_terms =
        match AtomMap.find_opt atom env.rec_atoms with
        | None ->
            type_terms
        | Some i ->
            assert (type_terms = []);
            Jlist.make i (fun i' -> `Var (DeBruijn.of_int (i-i'-1)))
      in
      let instance = `Instance (`Var atom) in
      List.fold_left app instance type_terms

  | `App (expr, exprs) ->
      let exprs = expr :: exprs in
      let exprs = List.map (desugar_expr env) exprs in
      `App (List.hd exprs, List.tl exprs)

  | `Function (arg_type, pat_exprs) ->
      (* This is the regular desugaring function. We try a few tricks before
       * resorting to it in order to simplify the AST we generate. *)
      let desugar_function () =
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
        let instance = `Instance var in
        let arg_type = desugar_type env arg_type in
        (* No wrap_forall here since in ML arguments to functions are not polymorphic *)
        (* Translate the expressions and the patterns *)
        let gen (pat, expr) =
          let pat, atoms = desugar_pat env pat in
          let pat = add_coercions_to_pattern env pat arg_type in
          let new_env = introduce atoms env in
          let expr = desugar_expr new_env expr in
          (pat, expr)
        in
        (* Finally return fun x -> match x with [...] *)
        let mmatch = `Match (instance, (List.map gen pat_exprs)) in
        `Fun (var, arg_type, mmatch)
      in
      begin match pat_exprs with
        (* We deal with the trivial case fun x -> where x is already an identifier *)
        | [(`Var _ as v, expr)] ->
            let arg_type = desugar_type env arg_type in
            let pat, atoms = desugar_pat env v in
            let pat = add_coercions_to_pattern env pat arg_type in
            begin match pat, atoms with
            | (`Var _ as v), ([_] as atoms) ->
                let new_env = introduce atoms env in
                `Fun (v, arg_type, desugar_expr new_env expr)
            | _ ->
                desugar_function ()
            end

        (* This is the general case. We either have many branches, or a
         * pattern instead of a single var. *)
        | _ ->
            desugar_function ()
      end

  | `Match (expr, { young_vars; f_type_term = type_term }, pat_exprs) ->
      let expr = desugar_expr env expr in
      let expr = wrap_lambda young_vars expr in
      let type_term = desugar_type env type_term in
      let type_term = wrap_forall young_vars type_term in
      let gen (pat, expr) =
        let pat, atoms = desugar_pat env pat in
        let sub_env = introduce atoms env in
        let pat =
          Error.debug "[DesugarMatch] Adding coercions to match %s\n"
            (DeBruijn.string_of_type_term type_term);
          add_coercions_to_pattern sub_env pat type_term
        in
        let expr = 
          desugar_expr sub_env expr
        in
        (pat, expr)
      in
      let pat_exprs = List.map gen pat_exprs in
      `Match (expr, pat_exprs)

  | `Tuple exprs ->
      let exprs = List.map (desugar_expr env) exprs in
      `Tuple exprs

  | `Construct (t, ts, cons, args) ->
      let e = `Construct (cons, List.map (desugar_expr env) args) in
      let t = StringMap.find t env.atom_of_type in
      let ts = List.map (desugar_type env) ts in
      let c = `Fold (t, ts) in
      `Coerce (e, c)

  | `Const c ->
      let c = desugar_const c in
      `Const c

  | `Sequence (e1, e2) ->
      `Sequence (desugar_expr env e1, desugar_expr env e2)

  | `IfThenElse (_if_expr, _then_expr, _else_expr) ->
      failwith "TODO: desugar if-then-else"

  | `AssertFalse t ->
      `Magic (desugar_type env t)

  | `Magic t ->
      `Magic (desugar_type env t)

and desugar_letrec
    (env: env)
    (pat_coerc_exprs: (f_pattern * f_clblock * f_expression) list)
    : env * (pattern * type_term * expression) list =

  (* We first make a big pass to generate all the patterns, which in turn
   * generates all the atoms we need. *)
  let new_patterns, new_atoms =
    List.split
      (List.map (fun (pat, _, _) -> desugar_pat env pat) pat_coerc_exprs)
  in
  (* Each pattern is actually a variable. We introduce all these in the
   * environment *)
  List.iter (fun l -> assert (List.length l = 1)) new_atoms;
  let new_atoms = List.flatten new_atoms in
  let env = introduce new_atoms env in
  (* The convention is: the information is in the first clblock *)
  let _, { young_vars; _ }, _ = List.hd pat_coerc_exprs in
  (* Assume we know all the atoms *)
  let rec_env = enter_letrec env new_atoms young_vars in
  (* To type the branches *)
  let var_type_exprs = List.map2
    (fun pat (_, { young_vars; f_type_term }, expr) ->
      (* Desugar the type *)
      let f_type_term = desugar_type rec_env f_type_term in
      let type_term = wrap_forall young_vars f_type_term in
      (* The pattern was already generated in a first pass. So we use the one
       * that was generated before, and we enrich it with coercions now we know
       * its type. *)
      let pat = add_coercions_to_pattern rec_env pat type_term in
      (* And now the expression *)
      let e = desugar_expr rec_env expr in
      let e = wrap_lambda young_vars e in
      (pat, type_term, e)
    )
    new_patterns
    pat_coerc_exprs
  in
  env, var_type_exprs

(* This function only translates stupidly a f_pattern into a Core.pattern. If we
 * are in a situation that requires that we generate a coercion, then
 * add_coercions_to_pattern will be called. It will enrich the translated
 * pattern with the required coercions to "make everything work". *)
and desugar_pat
    (env: env)
    ?(rebind: unit option)
    (pat: f_pattern)
    : pattern * Atom.t list =
  match pat with
  | `Var ident ->
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
       * premade_env. *)
      Error.debug "[DOr] Orpat in\n";
      let p1, a1 = desugar_pat ?rebind env p1 in
      let premade_env = introduce a1 env in
      let p2, a2 = desugar_pat premade_env ~rebind:() p2 in
      assert (List.length a2 = 0);
      Error.debug "[DOr] Orpat out\n";
      `Or (p1, p2), a1

  | `Construct (cons, args) ->
      let args, introduced_atoms = List.split (List.map (desugar_pat env) args) in
      `Construct (cons, args), List.flatten introduced_atoms

  | `Alias _ ->
      failwith "TODO: desugar alias patterns"

  | `Const c ->
      `Const (desugar_const c), []

  | `Any ->
      `Any, []

(* [add_coercions_to_pattern] walks down the pattern and the pattern type in
 * parallel, and returns a list of coercions needed to properly
 * type this pattern. The expected workflow is:
 *  - obtain a f_type_term (possibly with the number of generalized variables from a clblock)
 *  - call desugar_type
 *  - call wrap_forall if needed
 *  - call add_coercions_to_pattern
 * *)
and add_coercions_to_pattern
    (env: env)
    (pat: pattern)
    (typ: type_term)
    : pattern =

  let compose c1 c2 =
    match c1, c2 with
    | `Id, c1 -> c1
    | c2, `Id -> c2
    | _ -> `Compose (c1, c2)
  in 

  let forall_covar c =
     if c = `Id then `Id else `ForallCovar c
  in

  let covar_tuple i c =
    if c = `Id then `Id else `CovarTuple (i, c)
  in

  let coerce p1 c1 =
    if c1 = `Id then p1 else `Coerce (p1, c1)
  in

  let push_n_foralls_inside n what =
    let rec fold n =
      if n = 0 then
          `Id
      else
        let c = fold (n - 1) in
        let c1 = if c = `Id then `Id else `ForallCovar c in
        compose c1 what
    in
    fold n
  in

  (* Instead of returning a pattern every time and possibly using
   *  `Coerce (`Coerce ( ... ) ... )
   * we batch coercions as much as we can by returning a pattern + a coercion
   * instead of just a pattern with coercions inside. *)
  let rec generate_coerc
          (env: env)
          (pat: pattern)
          (typ: DeBruijn.type_term)
          : pattern * coercion =
    match pat with
    | `Tuple patterns ->
        let forall, bare_term = strip_forall typ in
        Error.debug "Matching a tuple-pattern against type %s\n"
          (DeBruijn.string_of_type_term typ);
        begin match bare_term with
        | `Cons (head_symbol, cons_args) ->
            assert (head_symbol = Algebra.TypeCons.head_symbol_tuple (List.length patterns));
            (* Recursively generate the coercions for each of the branches *)
            let gen i pattern type_term =
              let pattern, c =
                generate_coerc env pattern (wrap_forall forall type_term)
              in
              pattern, covar_tuple i c
            in
            (* We have the first coercion *)
            let patterns, coercions = List.split (Jlist.map2i gen patterns cons_args) in
            let c = Jlist.concat compose coercions in
            (* Explain that we inject all the variables inside the branches *)
            let c0 = push_n_foralls_inside forall `DistribTuple in
            `Tuple patterns, `Compose (c0, c)
        | _ ->
            assert false
        end

    | `Var _ ->
        let forall, bare_term = strip_forall typ in
        (* Mark all the variables quantified in this scheme
           XXX this probably has a bad complexity *)
        let seen = Array.make forall false in
        let rec walk type_term =
          match type_term with
            | `Var v ->
                let i = DeBruijn.index v in
                if i < forall then
                  seen.(DeBruijn.index v) <- true
            | `Cons (_head_symbol, cons_args) ->
                List.iter walk cons_args
            | `Forall t ->
                walk t
            | `Named (_, ts) ->
                List.iter walk ts
            | `Prod ts
            | `Sum ts ->
                List.iter (fun (_, ts) -> List.iter walk ts) ts
        in
        walk bare_term;
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
               forall_covar c
        in
        pat, fold forall

    | `Or (p1, p2) ->
        let p1, c1 = generate_coerc env p1 typ in
        let p2, c2 = generate_coerc env p2 typ in
        let p1 = coerce p1 c1 in
        let p2 = coerce p2 c2 in
        `Or (p1, p2), `Id

    | `Const x ->
        `Const x, `Id

    | `Any ->
        `Any, `Id

    | `Coerce _ ->
        Error.debug "This pattern already has coercions! You probably called \
          add_coercions_to_pattern twice. Please check your code.\n";
        failwith "Fatal."
                  
    | _ ->
        Error.debug "Trying to generate a coercion for type %s\n"
          (DeBruijn.string_of_type_term typ);
        failwith "Only supporting coercions for tuples at the moment\n"
  in
  let pat, coerc = generate_coerc env pat typ in
  if coerc = `Id then pat else `Coerce (pat, coerc)

and desugar_const const =
  match const with
  | `Float f ->
      let f = float_of_string f in
      `Float f

  | `Char _ | `Int _ | `String _ as x ->
      x

and desugar_struct
    ((env, acc): env * structure)
    (str: f_structure_item)
    : env * structure =
  match str with
  | `Let (rec_flag, pat_coerc_exprs) ->
      if rec_flag then
        let new_env, var_type_exprs =
          desugar_letrec
            env
            pat_coerc_exprs
        in
        let extra_coercions, var_type_exprs = List.split (List.map
          (fun (var, typ, expr) ->
            match var with
            | `Coerce (`Var _ as var, _) as pat ->
                Some (`Let (pat, `Instance var)), (var, typ, expr)
            | `Var _ as var ->
                None, (var, typ, expr)
            | _ ->
                assert false
          )
          var_type_exprs)
        in
        let extra_coercions = Jlist.filter_some extra_coercions in
        Error.debug "[TLetRec] In this let-rec, %d identifiers need coercions\n"
          (List.length extra_coercions);
        new_env,
        List.flatten [extra_coercions; [`LetRec var_type_exprs]; acc]

      else
        let new_patterns, new_atoms =
          List.split
            (List.map (fun (pat, _, _) -> desugar_pat env pat) pat_coerc_exprs)
        in
        let new_atoms = List.flatten new_atoms in
        let new_env = introduce new_atoms env in
        (* And then we desugar all of the initial branches in the same previous
         * scope *)
        let gen_branch (_, { young_vars; f_type_term = type_term }, e1) pat = 
          let e1 = desugar_expr env e1 in
          (* Beware, now we must generate proper F terms *)
          (* So we generate proper Lambdas *)
          let e1 = wrap_lambda young_vars e1 in
          (* Generate the coercion *)
          let type_term = desugar_type env type_term in
          let type_term = wrap_forall young_vars type_term in
          let new_pat = add_coercions_to_pattern new_env pat type_term in
          `Let (new_pat, e1)
        in
        new_env,
        List.map2 gen_branch pat_coerc_exprs new_patterns @ acc

  | `Type user_type ->
      let name = user_type # name in
      let arity = user_type # arity in
      let fields = user_type # fields in
      let atom = Atom.fresh (ident name Location.none) in
      let env = register_user_type env name atom in
      let fields = List.map
        (fun (l, ts) -> (l, List.map (desugar_type env) ts)) fields
      in
      (* We enforce the invariant that this list is sorted *)
      let fields = List.sort
        (fun (x, _) (y, _) -> compare x y)
        fields
      in
      match user_type # kind with
      | `Variant ->
          let t =
            `Type (arity, atom, `Sum fields)
          in
          env, t :: acc
      | `Record ->
          failwith "TODO: implement `Record data types in core"


and desugar_type
    (env: env)
    (t: f_type_term)
    : DeBruijn.type_term =
  (match t with
  | `Var _ as v ->
      (v: f_type_term :> DeBruijn.type_term)
  | `Cons ( { cons_name; _ }, cons_args ) as c ->
      begin match StringMap.find_opt cons_name env.atom_of_type with
      | Some atom ->
          `Named (atom, (cons_args: f_type_term list :> DeBruijn.type_term list))
      | None ->
          (c: f_type_term :> DeBruijn.type_term)
      end
  | `Forall t ->
      `Forall (desugar_type env t))


let desugar structure =
  let env = { atom_of_ident = IdentMap.empty; rec_atoms = AtomMap.empty; atom_of_type = StringMap.empty } in
  let _toplevel_env, structure =
    List.fold_left desugar_struct (env, []) structure
  in
  List.rev structure


module PrettyPrinting = struct

  let pcolor ?l c s =
    let l = Option.map_none (String.length s) l in
    Pprint.fancystring (Bash.color c "%s" s) l

  let arrow = pcolor Bash.colors.Bash.yellow "->"

  let keyword k = pcolor Bash.colors.Bash.yellow k

  let string_of_type_term t = Pprint.string (DeBruijn.string_of_type_term t)

  let rec doc_of_expr: expression -> Pprint.document = 
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

      | `LetRec (map, e2) ->
          let letdoc = pcolor colors.yellow "let rec" in
          let anddoc = pcolor colors.yellow "and" in
          let branches = List.map
            (fun (p, t, e) ->
              let pdoc = doc_of_pat (p: var :> pattern) in
              let tdoc = string (DeBruijn.string_of_type_term t) in
              let edoc = doc_of_expr e in
              pdoc ^^ colon ^^ space ^^ tdoc ^^ space ^^ equals ^^ space ^^
              (nest 2 (break1 ^^ edoc)))
            map
          in
          let branches = Jlist.concat
            (fun x y -> x ^^ break1 ^^ anddoc ^^ space ^^ y)
            branches
          in
          let indoc = pcolor colors.yellow "in" in
          let e2 = doc_of_expr e2 in
          letdoc ^^ space ^^ branches ^^ 
          break1 ^^ indoc ^^ break1 ^^
          e2

      | `Fun (`Var v, t, e2) ->
          let vdoc = string (Atom.string_of_atom v) in
          let t = string (DeBruijn.string_of_type_term t) in
          let vdoc = lparen ^^ vdoc ^^ colon ^^ space ^^ t ^^ rparen in
          let e2 = doc_of_expr e2 in
          let edoc = nest 2 (break1 ^^ e2) in
          (pcolor 207 ~l:1 "λ") ^^ space ^^ vdoc ^^ space ^^ arrow ^^ space ^^ edoc

      | `Instance (`Var atom) ->
          string (Atom.string_of_atom atom)

      | `App (e1, args) ->
          let e1 = lparen ^^ (doc_of_expr e1) ^^ rparen in
          Jlist.concat (fun x y -> x ^^ space ^^ y) (e1 :: (List.map doc_of_expr args))

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
          let pat_exprs = Jlist.concat (fun x y -> x ^^ break1 ^^ y) pat_exprs in
          let matchdoc = pcolor colors.yellow "match" in
          let withdoc = pcolor colors.yellow "with" in
          matchdoc ^^
            (nest 2 (break1 ^^ edoc)) ^^ break1 ^^ withdoc ^^
          (nest 2 (break1 ^^ pat_exprs))

      | `Sequence (e1, e2) ->
          (doc_of_expr e1) ^^ semi ^^ break1 ^^ (doc_of_expr e2)

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
          let edoc = Jlist.concat (fun x y -> x ^^ comma ^^ space ^^ y) edocs in
          lparen ^^ edoc ^^ rparen

      | `Const c ->
          doc_of_const c

      | `Magic t ->
          (string "%magic: ") ^^ (string (DeBruijn.string_of_type_term t))

      | `Coerce (expr, coerc) ->
          let edoc = doc_of_expr expr in
          let cdoc = doc_of_coerc coerc in
          let triangle = pcolor colors.green ~l:1 "▸" in
          edoc ^^ space ^^ triangle ^^ space ^^ cdoc

      | `Construct (label, args) ->
          let l = List.length args in
          if l > 1 then
            (string label) ^^ space ^^ (doc_of_expr (`Tuple args))
          else if l = 1 then
            (string label) ^^ space ^^ (doc_of_expr (List.hd args))
          else
            (string label)

  and doc_of_pat: pattern -> Pprint.document =
    let open Pprint in
    let open Bash in
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

      | `Var atom ->
          string (Atom.string_of_atom atom)

      | `Construct (label, args) ->
          let l = List.length args in
          if l > 1 then
            (string label) ^^ space ^^ (doc_of_pat (`Tuple args))
          else if l = 1 then
            (string label) ^^ space ^^ (doc_of_pat (List.hd args))
          else
            (string label)

      | `Const c ->
          doc_of_const c

      | `Coerce (pat, coerc) ->
          let pdoc = doc_of_pat pat in
          let cdoc = doc_of_coerc coerc in
          let triangle = pcolor colors.green ~l:1 "▸" in
          pdoc ^^ space ^^ triangle ^^ space ^^ cdoc

  and doc_of_const: const -> Pprint.document =
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

  and doc_of_coerc: coercion -> Pprint.document =
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
          (fancystring "∀" 3) ^^ lbracket ^^ c ^^ rbracket

      | `ForallElim arg ->
          let arg = string (DeBruijn.string_of_type_term arg) in
          (fancystring "•" 1) ^^ lbracket ^^ arg ^^ rbracket 

      | `CovarTuple (i, coercion) ->
          let coercion = doc_of_coerc coercion in
          let i = string (string_of_int i) in
          (string "×") ^^ i ^^ lbracket ^^ coercion ^^ rbracket

      | `DistribTuple ->
          fancystring "∀×" 2

      | `Unfold (t, ts) ->
          let args = doc_of_args ts in
          let t = Atom.string_of_atom t in
          (string "unfold") ^^ lbracket ^^ args ^^ (string t) ^^ rbracket

      | `Fold (t, ts) ->
          let args = doc_of_args ts in
          let t = Atom.string_of_atom t in
          (string "fold") ^^ lbracket ^^ args ^^ (string t) ^^ rbracket

  and doc_of_args ts =
    let open Pprint in
    let arity = List.length ts in
    let args = List.map string_of_type_term ts in
    if arity > 1 then
      lparen ^^ (Jlist.concat (fun x y -> x ^^ comma ^^ space ^^ y) args)
      ^^ rparen ^^ space
    else if arity = 1 then
      List.hd args ^^ space
    else
      empty

  and doc_of_struct: structure -> Pprint.document =
    let open Pprint in
    let open Bash in
    let doc_of_str =
      function
      | `Let (pat, e1) ->
        let letdoc = pcolor colors.yellow "let" in
        let pdoc = doc_of_pat pat in
        let e1 = doc_of_expr e1 in
        letdoc ^^ space ^^ pdoc ^^ space ^^ equals ^^ 
          (nest 2 (break1 ^^ e1))

      | `LetRec l ->
          let letdoc = pcolor colors.yellow "let rec" in
          let anddoc = pcolor colors.yellow "and" in
          let branches = List.map
            (fun (p, t, e) ->
              let pdoc = doc_of_pat (p: var :> pattern) in
              let tdoc = string (DeBruijn.string_of_type_term t) in
              let edoc = doc_of_expr e in
              pdoc ^^ colon ^^ space ^^ tdoc ^^ space ^^ equals ^^ space ^^
              (nest 2 (break1 ^^ edoc)))
            l
          in
          let branches = Jlist.concat
            (fun x y -> x ^^ break1 ^^ break1 ^^ anddoc ^^ space ^^ y)
            branches
          in
          letdoc ^^ space ^^ branches
      | `Type (arity, name, t) ->
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
                List.rev (build (arity-1))
              in
              let args = Jlist.concat (fun x y -> x ^^ comma ^^ space ^^ y) onetwothree in
              let args = if arity > 1 then lparen ^^ args ^^ rparen else args in
              args ^^ space
            else
              empty
          in
          let typedoc = pcolor colors.yellow "type" in
          let tdoc = string_of_type_term t in
          typedoc ^^ space ^^ args ^^ (string (Atom.string_of_atom name))
          ^^ space ^^ equals ^^ space ^^ tdoc
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
