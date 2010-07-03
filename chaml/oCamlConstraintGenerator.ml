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
open Error

module Make(S: Algebra.SOLVER) = struct

  module StringMap = Jmap.Make(String)
  module Constraint_ = Constraint.Make(S)
  open Constraint_
  open Algebra.Core
  open Algebra.TypeCons
  open Algebra.Identifiers

  let string_of_constraint = PrettyPrinter.string_of_constraint

  (* This is error handling. Add new errors here *)
  type error =
    | NotImplemented of string * Location.t
    | VariableBoundSeveralTimes of string * Location.t
    | VariableMustOccurBothSides of string * Location.t
    | AlgebraError of Algebra.Core.error
    | OnlyIdentInLetRec of Location.t
    | TypeConstructorArguments of string * int * int * Location.t

  exception Error of error
  let raise_error e = raise (Error e)

  let string_of_error =
    let print_loc () { Location.loc_start; Location.loc_end; Location.loc_ghost } =
      let open Lexing in
      assert (not loc_ghost);
      let { pos_fname; pos_lnum; pos_bol; _ } = loc_start in
      let { pos_bol = pos_end; _ } = loc_end in
      Printf.sprintf "File %s, line %d, characters %d-%d"
        pos_fname pos_lnum pos_bol pos_end
    in function
    | NotImplemented (r, loc) ->
        Printf.sprintf
          "%a: the following OCaml feature is not implemented: %s\n"
          print_loc loc r
    | VariableBoundSeveralTimes (v, loc) ->
        Printf.sprintf
          "%a: variable %s is bound several times in the matching\n"
          print_loc loc v
    | VariableMustOccurBothSides (v, loc) ->
        Printf.sprintf
          "%a: variable %s must occur on both sides of this pattern\n"
          print_loc loc v
    | OnlyIdentInLetRec loc ->
        Printf.sprintf
          "%a: only variables are allowed as the left-hand side of `let rec'\n"
          print_loc loc
    | TypeConstructorArguments (s, n1, n2, loc) ->
        Printf.sprintf
          "%a: type constructor %s expects %d arguments, but you gave it %d"
          print_loc loc s n1 n2
    | AlgebraError e ->
        Algebra.Core.string_of_error e

  (* Small helpers functions that don't belong to the main logic. *)
  let dont_bind_several_times pexp_loc map new_map =
    let inter = IdentMap.inter map new_map in
    if (not (IdentMap.is_empty inter)) then begin
      let bad_ident = List.hd (IdentMap.keys inter) in
      let bad_ident = string_of_ident bad_ident in
      raise_error (VariableBoundSeveralTimes (bad_ident, pexp_loc));
    end

  let bind_both_sides ppat_loc map1 map2 =
    let xor_map = IdentMap.xor map1 map2 in
    if not (IdentMap.is_empty xor_map) then begin
      let bad_ident = string_of_ident (List.hd (IdentMap.keys xor_map)) in
      raise_error (VariableMustOccurBothSides (bad_ident, ppat_loc))
    end

  (* Convenience shortcuts *)
  type camlx_pattern = CamlX.Make(S).pattern
  type camlx_expression = CamlX.Make(S).expression
  type camlx_structure = CamlX.Make(S).structure
  type camlx_const = CamlX.Make(S).const
  type camlx_user_type = CamlX.Make(S).user_type

  (* Instead of returning 4-uples each time, the main functions
   * generate_constraint_pattern, generate_constraint_expression... return
   * records. *)
  type constraint_pattern = {
    p_constraint: type_constraint;
    pat: camlx_pattern;
    var_map: (S.var type_var * S.scheme) IdentMap.t;
    introduced_vars: S.var type_var list;
  }

  type constraint_expression = {
    e_constraint: type_constraint;
    expr: camlx_expression;
  }

  type constraint_scheme = {
    scheme: type_scheme;
    pat_expr: camlx_pattern * S.pscheme * camlx_expression;
  }

  (* These are just convenient helpers *)
  let fresh_type_var ?letter () =
    let prefix = Option.map (String.make 1) letter in
    `Var (S.new_var (fresh_name ?prefix ()))

  let new_scheme (`Var uvar) =
    S.new_scheme_for_var uvar

  let new_pscheme (`Var uvar) =
    S.new_pscheme_for_var uvar

  let random_ident_name () = Filename.basename (Filename.temp_file "" "")


  (* We're forwarding an environment through all the recursive calls. It only
   * contains a mapping from data constructors to their types. *)

  (* Very naïve representation of data types.
   *
   * Example:
   *   type ('a, 'b) t = Nil | Cons of 'a * ('a, 'b) t
   * becomes
   *   tc == { "t"; 2 },
   *   [("Nil", []); ("Cons", [0; `Cons (t, [0; 1])])]
   * *)
  type data_constructor = string * int type_term list
  type data_type = type_cons * data_constructor list

  (* Because we're using physical equality for head symbols, we keep a mapping
   * from type names to head symbols. *)
  type env = {
    data_type_of_constructor: data_type StringMap.t;
    head_symbol_of_type: type_cons StringMap.t;
  }
  let env = {
    data_type_of_constructor = StringMap.empty;
    head_symbol_of_type = StringMap.empty;
  }

  (* This enriches the environment with a mapping from the type name to the
   * globally unique head symbol *)
  let register_data_type: env -> type_cons -> env =
    fun { data_type_of_constructor; head_symbol_of_type } type_cons -> {
      data_type_of_constructor;
      head_symbol_of_type =
        StringMap.add type_cons.cons_name type_cons head_symbol_of_type
    }

  (* This enriches the environment with a mapping from one constructor (Nil,
   * for example) to its corresponding data type. *)
  let register_data_constructor: env -> data_constructor -> data_type -> env =
    fun { data_type_of_constructor; head_symbol_of_type } data_constructor data_type ->
      let data_type_of_constructor =
        StringMap.add (fst data_constructor) data_type data_type_of_constructor
      in
      { data_type_of_constructor; head_symbol_of_type }

  (* This functions is used to register in the environment all the constructors
   * for a given data type. *)
  let register_data_constructors: env -> type_cons -> data_constructor list -> env =
    fun env head_symbol data_constructors ->
      let data_type = head_symbol, data_constructors in
      let env = List.fold_left
        (fun env data_constructor ->
          register_data_constructor env data_constructor data_type)
        env
        data_constructors
      in
      env

  let head_symbol_of_type { head_symbol_of_type; _ } data_type =
    StringMap.find data_type head_symbol_of_type

  let data_type_of_constructor { data_type_of_constructor; _ } data_constructor =
    StringMap.find data_constructor data_type_of_constructor

  let tuple_or_not loc cons_name l1 args =
    let l2 = List.length args in
    if l1 = 1 && l2 > 1 then
      [type_cons_tuple args]
    else if l1 > 1 && l1 = l2 then
      args
    else
      raise_error (TypeConstructorArguments (cons_name, l1, l2, loc))

  let copy_data_constructor env k =
    (* XXX bad complexity, maybe change the abstractions? *)
    let head_symbol, data_constructors = data_type_of_constructor env k in
    let cons_name, type_terms =
      List.find (fun (k', _) -> k = k') data_constructors
    in
    assert (cons_name = k);
    let mapping =
      Array.init head_symbol.cons_arity (fun _ -> fresh_type_var ~letter:'d' ())
    in
    let type_terms =
      let rec convert = function
        | `Var i ->
            tv_tt mapping.(i)
        | `Cons (head_symbol, args) ->
            `Cons (head_symbol, List.map convert args)
      in
      List.map convert type_terms
    in
    head_symbol, Array.to_list mapping, type_terms

  let parse_typedecl: env -> (string * type_declaration) list -> env * camlx_user_type =
    let parse_typedecl: env -> string * type_declaration -> env * camlx_user_type =
      fun env (ptype_name, {
          ptype_params;
          ptype_cstrs = _;
          ptype_kind;
          ptype_private = _;
          ptype_manifest = _;
          ptype_variance = _;
          ptype_loc = _;
        }) ->
          match ptype_kind with
          | Ptype_variant constructors ->
              let params = Jlist.fold_lefti
                (fun i acc x -> StringMap.add x i acc)
                StringMap.empty
                ptype_params
              in
              let arity = List.length ptype_params in
              let head_symbol = {
                  cons_name = ptype_name;
                  cons_arity = arity;
                }
              in
              let env = register_data_type env head_symbol in
              let rec convert_core_type { ptyp_desc; ptyp_loc } =
                match ptyp_desc with
                | Ptyp_var v -> 
                    `Var (StringMap.find v params)
                | Ptyp_tuple ts ->
                    type_cons_tuple (List.map convert_core_type ts)
                | Ptyp_arrow (_, t1, t2) ->
                    type_cons_arrow (convert_core_type t1) (convert_core_type t2)
                | Ptyp_constr (Longident.Lident t, ts) ->
                    (* This can be ('a, 'b) t for instance *)
                    Error.debug "[CG] Type lookup %s\n" t;
                    let head_symbol = head_symbol_of_type env t in
                    let ts = List.map convert_core_type ts in
                    if List.length ts <> head_symbol.cons_arity then
                      raise_error (TypeConstructorArguments (
                        head_symbol.cons_name,
                        head_symbol.cons_arity,
                        List.length ts,
                        ptyp_loc));
                    `Cons (head_symbol, ts)
                | _ ->
                    failwith "Dunno what to do with this core type"
              in
              let parse_constructor (cons_name, core_types, _cons_loc) =
                (cons_name, List.map convert_core_type core_types)
              in
              let constructors = List.map parse_constructor constructors in
              register_data_constructors
                env
                head_symbol
                constructors,
              object
                method user_type_arity = arity
                method user_type_kind  = `Variant
                method user_type_fields = constructors
              end

          | _ ->
              failwith "Unsupported data type"
    in
    fun env -> function
      | [typedecl] ->
          parse_typedecl env typedecl
      | _ ->
          failwith "Cannot parse simulatenous type decls"

  (* This one is defined a bit later because it depends on env (not useful yet
   * but who knows?) *)
  type let_info = {
    env: env;
    constr_scheme: type_scheme list;
    camlx_pat_expr: (camlx_pattern * S.pscheme * camlx_expression) list;
    rec_flag: bool;
  }

  (* Returns c_1 and (c_2 and ( ... and c_n)) *)
  let constr_conj = function
    | hd :: tl ->
        List.fold_left (fun x y -> `Conj (x, y)) hd tl
    | [] ->
        `True

  (* We nest functions that way so that all the options that are passed to
   * generate_constraint are available to generate_constraint_pattern,
   * generate_constraint_expression and others... *)
  let generate_constraint =
    fun ~generalize_match:opt_generalize_match
        ~default_bindings:opt_default_bindings
        structure ->

    (* Parsetree.pattern
     *
     * We are given a type var that's supposed to match the given pattern. What
     * we return is a type constraint and a map from identifiers to the
     * corresponding type variables. For instance, generate_constraint_pattern X
     * (a*b) returns \exists Y Z. [ X = Y * Z and a < X and b < Y ] and { a =>
     * Y; b => Z }
     *
     * We also return the list of all the variables that have been generated and
     * must be bound existentially for this pattern. The let - binding that
     * encloses us will generate the `Exists constraint for us.
     *
     * NB: one might be tempted to think that the map's keys and the list of
     * existentially bound variables are equal. This is not necessarily true, as
     * we might generate intermediate existential variables that are not bound
     * to a specific identifier.
     *
     * *)
    let rec generate_constraint_pattern:
          env ->
          S.var type_var ->
          pattern ->
          constraint_pattern
        =
      fun env x { ppat_desc; ppat_loc } ->
      match ppat_desc with
        | Ppat_any ->
            {
              p_constraint = `True;
              var_map = IdentMap.empty;
              introduced_vars = [];
              pat = `Any;
            }

        | Ppat_var v ->
            let var = ident v ppat_loc in
            let solver_scheme = new_scheme x in
            let var_map = IdentMap.add var (x, solver_scheme) IdentMap.empty in
            {
              p_constraint = `True;
              var_map;
              introduced_vars = [];
              pat = `Var var;
            }

        | Ppat_tuple patterns ->
            let xis = List.map (fun _ -> fresh_type_var ()) patterns in
            let patterns = List.map2
              (fun pattern xi ->
                let { p_constraint = konstraint; var_map; introduced_vars; pat; } =
                  generate_constraint_pattern env xi pattern
                in
                konstraint, var_map, xi :: introduced_vars, pat)
              patterns
              xis
            in
            let pattern_constraint = constr_conj (List.map (fun (x, _, _, _) -> x) patterns) in
            let pattern_map = List.fold_left
              (fun known_map sub_map ->
                dont_bind_several_times ppat_loc known_map sub_map;
                IdentMap.union known_map sub_map
              )
              IdentMap.empty
              (List.map (fun (_, x, _, _) -> x) patterns)
            in
            let pattern_vars = List.flatten (List.map (fun (_, _, x, _) -> x) patterns) in
            let pat = `Tuple (List.map (fun (_, _, _, x) -> x) patterns) in
            let konstraint = `Equals (x, type_cons_tuple (tvl_ttl xis)) in
            let p_constraint = `Conj (konstraint, pattern_constraint) in
            {
              p_constraint;
              var_map = pattern_map;
              introduced_vars = pattern_vars;
              pat;
            }

        | Ppat_or (pat1, pat2) ->
            (* match e1 with p1 | p2 -> *)
            let { p_constraint = c1; var_map = map1; introduced_vars = vars1; pat = lp1 } =
              generate_constraint_pattern env x pat1
            in
            let { p_constraint = c2; var_map = map2; introduced_vars = vars2; pat = lp2 } =
              generate_constraint_pattern env x pat2
            in
            bind_both_sides ppat_loc map1 map2;
            (* If identifier i is bound to type variable x1 on the left and x2
             * on the right, this just generates the constraint "x1 = x2" *)
            let constraints =
              IdentMap.fold
                (fun k (v, _) acc ->
                   `Equals (fst (IdentMap.find k map2), tv_tt v) :: acc)
                map1
                []
            in
            {
              p_constraint = constr_conj (c1 :: c2 :: constraints);
              var_map = map1;
              introduced_vars = vars1 @ vars2;
              pat = `Or (lp1, lp2);
            }

        | Ppat_constant const ->
            let konstraint, constant =
              generate_constraint_constant env ppat_loc x const
            in
            {
              p_constraint = konstraint;
              var_map = IdentMap.empty;
              introduced_vars = [];
              pat = `Const constant
            }

        | Ppat_construct (Longident.Lident c, pat, _) ->
            let head_symbol, type_vars, type_terms = copy_data_constructor env c in
            let c0: type_constraint = `Equals (x, `Cons (head_symbol, tvl_ttl type_vars)) in
            let pats = match pat with
              | None ->
                  []
              | Some { ppat_desc = Ppat_tuple pats; _ } ->
                  pats
              | Some pat ->
                  [pat]
            in
            let l1 = List.length type_terms in
            let l2 = List.length pats in
            let pats =
              if l1 = 1 && l2 > 1 then
                [ { ppat_desc = Ppat_tuple pats; ppat_loc } ]
              else if l1 >= 0 && l1 = l2 then
                pats
              else
                raise_error (TypeConstructorArguments (c, l1, l2, ppat_loc))
            in
            let patterns = List.map2
              (fun pat type_term ->
                let xi = fresh_type_var ~letter:'e' () in
                let { p_constraint; var_map; introduced_vars; pat } =
                  generate_constraint_pattern env xi pat
                in
                let konstraint = `Equals (xi, type_term) in
                let konstraint = `Conj (konstraint, p_constraint) in
                konstraint, var_map, xi :: introduced_vars, pat)
              pats
              type_terms
            in
            let konstraint = constr_conj (List.map (fun (x, _, _, _) -> x) patterns) in
            let var_map = List.fold_left
              (fun known_map sub_map ->
                dont_bind_several_times ppat_loc known_map sub_map;
                IdentMap.union known_map sub_map
              )
              IdentMap.empty
              (List.map (fun (_, x, _, _) -> x) patterns)
            in
            let introduced_vars =
              type_vars @ List.flatten (List.map (fun (_, _, x, _) -> x) patterns)
            in
            let konstraint = `Conj (konstraint, c0) in
            let pat = `Construct (c, List.map (fun (_, _, _, x) -> x) patterns) in
            {
              p_constraint = konstraint;
              var_map;
              introduced_vars;
              pat;
            }

        | _ ->
            raise_error (NotImplemented ("some pattern", ppat_loc))

    and generate_constraint_constant:
          env ->
          Location.t ->
          S.var type_var ->
          Asttypes.constant ->
          type_constraint * camlx_const
        =
      let open Asttypes in
      fun _env pexp_loc t -> function
        | Const_int x ->
            `Equals (t, type_cons_int), `Int x
        | Const_char x ->
            `Equals (t, type_cons_char), `Char x
        | Const_string x ->
            `Equals (t, type_cons_string), `String x
        | Const_float x ->
            `Equals (t, type_cons_float), `Float x
        | _ ->
            raise_error (NotImplemented ("int32 or int64 or intnative", pexp_loc))

    (* Parsetree.expression
     *
     * - TODO figure out what label and the expression option are for in
     * Pexp_function then do things accordingly. label is probably when the
     * argument is labeled. What is the expression option for? -> Probably a
     * default value for ?blah arguments.
     *
     * *)
    and generate_constraint_expression:
          env ->
          S.var type_var ->
          expression ->
          constraint_expression
        =
      fun env t { pexp_desc; pexp_loc } ->
      match pexp_desc with
      | Pexp_ident (Longident.Lident x) ->
          let solver_instance = S.new_instance () in
          let ident = ident x pexp_loc in
          let e_constraint = `Instance (ident, t, solver_instance) in
          let expr = `Instance (ident, solver_instance) in
          { e_constraint; expr; }

      | Pexp_constant c ->
          let e_constraint, expr =
            generate_constraint_constant env pexp_loc t c
          in
          { e_constraint; expr = `Const expr; }

      | Pexp_function (_, _, pat_expr_list) ->
          (* As in the definition. We could generate fresh variables for each
           * branch of the pattern-matching. The conjunction would then force
           * them to be all equal. However, I find it nicer to share x1 and x2.
           * *)
          let x1 = fresh_type_var ~letter:'x' () in
          let x2 = fresh_type_var ~letter:'x' () in
          (* X1 -> X2 = T *)
          let arrow_constr: type_constraint =
            `Equals (t, type_cons_arrow (tv_tt x1) (tv_tt x2))
          in
          let generate_branch (pat, expr) =
            (* roughly [[ pat: X1 ]] *)
            let { p_constraint = c1; var_map; introduced_vars; pat } =
              generate_constraint_pattern env x1 pat
            in
            (* [[ t: X2 ]] *)
            let { e_constraint = c2; expr } = generate_constraint_expression env x2 expr in
            let let_constr = `Let ([[], c1, var_map, None], c2) in
            (* This allows to properly scope the variables that are inner to
             * each pattern. x1 and x2 are a level higher since they are shared
             * accross patterns. This wouldn't change much as the variables are
             * fresh anyway, but let's do that properly! *)
            `Exists (introduced_vars, let_constr), (pat, expr)
          in
          let constraints, patexprs =
            List.split (List.map generate_branch pat_expr_list)
          in
          let e_constraint =
            `Exists ([x1; x2], constr_conj (arrow_constr :: constraints))
          in
          (* We need to describe the type of the whole pattern. It's the same
           * process as below for the match. We KNOW no variables will be
           * generalized so we put None in the constraint above and the
           * solver asserts this. So the pscheme is just a record with an
           * empty list of young variables (that's correct) and a unification
           * var that precisely describes the type of the whole pattern. So
           * we're good! *)
          let pscheme = new_pscheme x1 in
          { e_constraint; expr = `Function (pscheme, patexprs) }

      | Pexp_apply (e1, label_expr_list) ->
          (* ti: xi *)
          let xis, sub_constraints = List.split
            (List.map
              (fun (_, expr) ->
                let xi = fresh_type_var ~letter:'x' () in
                xi, generate_constraint_expression env xi expr
              )
              label_expr_list
            )
          in
          let sub_constraints, terms =
            List.split
              (List.map (fun { e_constraint; expr } -> e_constraint, expr) sub_constraints)
          in
          (* build the type constructor t1 -> (t2 -> (... -> (tn -> t))) *)
          let arrow_type = List.fold_right type_cons_arrow (tvl_ttl xis) (tv_tt t) in
          (* \exists x1. *)
          let x1 = fresh_type_var ~letter:'x' () in
          (* x1 = t1 -> ... -> tn *)
          let equals_constr: type_constraint = `Equals (x1, arrow_type) in
          (* [[ e1: x1 ]] *)
          let { e_constraint = arrow_constr; expr = e1 } =
            generate_constraint_expression env x1 e1
          in
          (* combine both: [[ e1: t1 -> t2 -> ... -> tn -> t ]] *)
          let constr: type_constraint = `Conj (arrow_constr, equals_constr) in
          (* the leftmost expression is an arrow and all the arguments have the right type *)
          let konstraint =
            List.fold_left (fun c1 c2 -> `Conj (c1, c2)) constr sub_constraints
          in
          { 
            e_constraint = `Exists (x1 :: xis, konstraint);
            expr =  `App (e1, terms)
          }

      | Pexp_let (rec_flag, pat_expr_list, e2) ->
          (* Once again, the list of pattern/expressions is here because of
           * let ... and ... in e2 (multiple simultaneous definitions *)
          generate_constraint_let
            env
            rec_flag
            pat_expr_list
            pexp_loc
            begin
              fun { constr_scheme; camlx_pat_expr; rec_flag; env } ->
                let { e_constraint = c2; expr = expr_e2;  } =
                  generate_constraint_expression env t e2
                in {
                  e_constraint = `Let (constr_scheme, c2);
                  expr =  `Let (rec_flag, camlx_pat_expr, expr_e2);
                }
            end

      | Pexp_match (e1, pat_expr_list) ->
          if opt_generalize_match then
            (* We generalize here. See the draft version of ATTAPL p.98 for the
             * exact rule. The important part is that we generate a `Let
             * constraint for each branch. Instead of copying the base
             * constraint into each branch, we use a `Let-binding and add an
             * instanciation constraint into each branch. This allows us to
             * simplify the constraint beforehand and perform better.
             *
             * The CamlX.Make term that is created corresponds by default to a
             * generalized match.
             *)
            let print_var_name buf () =
              Buffer.add_string buf (PrettyPrinter.string_of_type_var t)
            in
            Error.debug
              "[CG] Generalizing match constraint on %a\n" print_var_name ();
            (* This is going to be simplified first *)
            let x1 = fresh_type_var ~letter:'x' () in
            let ident1 = ident (random_ident_name ()) Location.none in
            let { e_constraint = constr_e1; expr = term_e1 } =
              generate_constraint_expression env x1 e1
            in
            let generate_branch (pat, expr) =
              (* Create a fresh variable *)
              let y = fresh_type_var ~letter:'y' () in
              (* It's an instance of the scheme *)
              let solver_instance = S.new_instance () in
              let instance_constr = `Instance (ident1, y, solver_instance) in
              (* It also satisfies the constraints of the pattern *)
              let { p_constraint = c1; var_map; introduced_vars; pat } =
                generate_constraint_pattern env y pat
              in
              let c = constr_conj [instance_constr; c1] in
              (* Generate constraints for the expression *)
              let { e_constraint = c2; expr } =
                generate_constraint_expression env t expr
              in
              (* Why do we have generalized variables here? We're taking an
               * *instance* of e1 (as in "match e1 with ..."). This means the
               * scheme is duplicated, fresh variables are created, and are
               * possibly left generalized. However, when type-checking at the
               * very end of the process, we'll copy e1 (that already has
               * Lambdas) and do the pattern-matching, so those variables will
               * be redundant with those from e1. So we use them here and later
               * on, but they do not represent real Lambdas below the "->". *)
              let pscheme = new_pscheme y in
              let let_constr: type_constraint =
                `Let ([y :: introduced_vars, c, var_map, Some pscheme], c2)
              in
              let_constr, (pat, Some pscheme, expr)
            in
            let constraints, pat_exprs =
              List.split (List.map generate_branch pat_expr_list)
            in
            let solver_scheme = new_scheme x1 in
            let solver_pscheme = new_pscheme x1 in
            let map = IdentMap.add ident1 (x1, solver_scheme) IdentMap.empty in
            let scheme = [x1], constr_e1, map, Some solver_pscheme in
            (* The fake ident we introduce is not kept in the CamlX term we
             * generate. It's unimportant. *)
            {
              e_constraint = `Let ([scheme], constr_conj constraints);
              expr = `Match (term_e1, solver_pscheme, pat_exprs)
            }
          else
            let x1 = fresh_type_var ~letter:'x' () in
            let pscheme = new_pscheme x1 in
            let { e_constraint = constr_e1; expr = term_e1 } =
              generate_constraint_expression env x1 e1
            in
            let generate_branch (pat, expr) =
              let { p_constraint = c1; var_map; introduced_vars; pat } =
                generate_constraint_pattern env x1 pat
              in
              let { e_constraint = c2; expr } =
                generate_constraint_expression env t expr
              in
              let let_constr = `Let ([[], c1, var_map, None], c2) in
              `Exists (introduced_vars, let_constr), (pat, None, expr)
            in
            let constraints, pat_exprs = 
              List.split (List.map generate_branch pat_expr_list)
            in
            (* This rule doesn't generalize, ocaml-style. The [None] above
             * enforces the invariant that no variables are generalized here
             * (there's an assert in solver.ml).
             * So we are right to create the pscheme and never pass it to the
             * solver, because the solver won't have variables to put in
             * young_vars anyway. So the pscheme is just a pointer to the
             * unification variable that describes the type of the whole
             * pattern, and that's precisely what we want!
             *
             * The other way round would be to put [Some pscheme] and assert
             * later in translator.ml that no variables were generalized. This
             * is equivalent. *)
            {
              e_constraint = `Exists ([x1], constr_conj (constr_e1 :: constraints));
              expr = `Match (term_e1, pscheme, pat_exprs);
            }

      | Pexp_tuple (expressions) ->
          let generate exp =
            let xi = fresh_type_var ~letter:'u' () in
            let { e_constraint; expr; } = generate_constraint_expression env xi exp in
            xi, e_constraint, expr
          in
          let xis, constraints, expressions =
            Jlist.split3 (List.map generate expressions)
          in
          let konstraint =
            constr_conj (`Equals (t, type_cons_tuple xis) :: constraints)
          in
          let konstraint = `Exists (xis, konstraint) in
          let expr = `Tuple (expressions) in
          { e_constraint = konstraint; expr; }

      | Pexp_construct (Longident.Lident c, expr, _) ->
          let head_symbol, type_vars, type_terms = copy_data_constructor env c in
          let c0: type_constraint = `Equals (t, `Cons (head_symbol, tvl_ttl type_vars)) in
          let exprs = match expr with
            | None ->
                []
            | Some { pexp_desc = Pexp_tuple exprs; _ } ->
                exprs
            | Some expr ->
                [expr]
          in
          let l1 = List.length type_terms in
          let l2 = List.length exprs in
          let exprs =
            if l1 = 1 && l2 > 1 then
              [ { pexp_desc = Pexp_tuple exprs; pexp_loc } ]
            else if l1 >= 0 && l1 = l2 then
              exprs
            else
              raise_error (TypeConstructorArguments (c, l1, l2, pexp_loc))
          in
          let xis, constraints, exprs = Jlist.split3 (List.map2
            (fun expr type_term ->
              let xi = fresh_type_var ~letter:'e' () in
              let { e_constraint; expr; } =
                generate_constraint_expression env xi expr
              in
              let konstraint = `Equals (xi, type_term) in
              let konstraint = `Conj (konstraint, e_constraint) in
              xi, konstraint, expr)
            exprs
            type_terms)
          in
          let konstraint = `Exists (xis @ type_vars, constr_conj (c0 :: constraints)) in
          let expr = `Construct (c, exprs) in
          {
            e_constraint = konstraint;
            expr;
          }

      | _ ->
          raise_error (NotImplemented ("some expression", pexp_loc))

    (* This is used both by Pexp_let and Pstr_eval/Pstr_let. Glad we have
     * polymorphic recursion! *)
    and generate_constraint_let: 'a.
          env ->
          Asttypes.rec_flag ->
          (pattern * expression) list ->
          Location.t ->
          (let_info -> 'a) ->
          'a
        =
      fun env rec_flag pat_expr_list pexp_loc k ->
      match rec_flag with
      | Asttypes.Nonrecursive ->
          let run (acc, map) pat_expr =
            let { scheme; pat_expr; } =
              generate_constraint_scheme env pat_expr
            in
            let _, _, new_map, _ = scheme in
            dont_bind_several_times pexp_loc map new_map;
            let union = IdentMap.union map new_map in
            (scheme, pat_expr) :: acc, union
          in
          let constraints, pat_expr =
            List.split (fst (List.fold_left run ([], IdentMap.empty) pat_expr_list))
          in
          k {
            constr_scheme = constraints;
            camlx_pat_expr = pat_expr;
            rec_flag = false;
            env;
          }
      | Asttypes.Recursive ->
          let main_type_vars = ref [] in
          let pattern_constraints = ref [] in
          let common_introduced_vars = ref [] in
          let expression_constraints = ref [] in
          let common_ident_map = ref IdentMap.empty in
          let exprs = ref [] in
          let push l e = l := e :: !l in
          let gen (pat, expr) = 
            let x = fresh_type_var ~letter:'r' () in
            push main_type_vars x;
            let { p_constraint; var_map; introduced_vars; pat } =
              generate_constraint_pattern env x pat
            in
            if IdentMap.cardinal var_map > 1 then
              raise_error (OnlyIdentInLetRec pexp_loc);
            let p_constraint = `Exists (introduced_vars, p_constraint) in
            push pattern_constraints p_constraint;
            push common_introduced_vars introduced_vars;
            dont_bind_several_times pexp_loc !common_ident_map var_map;
            common_ident_map := IdentMap.union !common_ident_map var_map;
            let { e_constraint; expr } =
              generate_constraint_expression env x expr
            in
            push expression_constraints e_constraint;
            let pscheme = new_pscheme x in
            push exprs (pat, pscheme, expr);
          in
          List.iter gen pat_expr_list;
          let inner_scheme: type_scheme =
            [], constr_conj !pattern_constraints, !common_ident_map, None
          in
          let inner_constraint =
            `Let ([inner_scheme], constr_conj !expression_constraints)
          in
          let _, first_pscheme, _ = List.hd !exprs in
          let outer_scheme: type_scheme =
            !main_type_vars, inner_constraint, !common_ident_map, Some first_pscheme
          in
          k {
            constr_scheme = [outer_scheme];
            camlx_pat_expr = !exprs;
            rec_flag = true;
            env;
          }
      | Asttypes.Default ->
          raise_error (NotImplemented ("rec flag = default", pexp_loc))

    (* Parsetree.structure
     *
     * structure_items are only for top-level definitions inside modules
     * - Pstr_value is for let x = ...
     * - Pstr_eval is for let _ = ...
     *
     * For let x = ..., we use a fresh type variable T. After constraint
     * resolution is finished, the constraint on T will be the type of the
     * top-level binding we were looking for. The outermost var_map contains the
     * bindings that end up in the environment. A single let-binding can bind
     * multiple variables if the left-hand side is a pattern.
     *
     * The fact that pat_expr_list is a list is because of let ... and ... that
     * are defined simultaneously. We allow that through the type_scheme list in
     * `Let type.
     *
     * *)
    and generate_constraint_structure:
          env ->
          structure ->
          type_constraint * camlx_structure
        =
      fun env structure ->
        let rec generate_structure_items:
              env ->
              structure_item list ->
              type_constraint * camlx_structure
            =
          fun env -> function
            | { pstr_desc; pstr_loc } :: tl ->
                begin match pstr_desc with
                | Pstr_value (rec_flag, pat_expr_list) ->
                    let c2, str2  = generate_structure_items env tl in
                    generate_constraint_let
                      env
                      rec_flag
                      pat_expr_list
                      pstr_loc
                      begin
                        fun { constr_scheme; camlx_pat_expr; rec_flag; _ } ->
                          `Let (constr_scheme, c2),
                          `Let (rec_flag, camlx_pat_expr) :: str2
                      end

                | Pstr_eval expr ->
                    let c2, str2 = generate_structure_items env tl in
                    generate_constraint_let
                      env
                      Asttypes.Nonrecursive
                      [{ ppat_desc = Ppat_any; ppat_loc = Location.none }, expr]
                      pstr_loc
                      begin
                        fun { constr_scheme; camlx_pat_expr; rec_flag; _ } ->
                          `Let (constr_scheme, c2),
                          `Let (rec_flag, camlx_pat_expr) :: str2
                      end

                | Pstr_type typedecl ->
                    let new_env, camlx_user_type = parse_typedecl env typedecl in
                    let c2, str2 = generate_structure_items new_env tl in
                    c2,
                    `Type camlx_user_type :: str2

                | _ ->
                    raise_error (NotImplemented ("some structure item", pstr_loc))
                end
          | [] ->
              `Done, []
        in
        let default_bindings, default_let_bindings =
          let plus_scheme =
            let plus_var = fresh_type_var ~letter:'z' () in
            let plus_type =
              type_cons_arrow type_cons_int (type_cons_arrow type_cons_int type_cons_int)
            in
            let pos = Location.none in
            let solver_scheme = new_scheme plus_var in
            let solver_pscheme = new_pscheme plus_var in
            let ident = ident "+" pos in
            let plus_map = IdentMap.add ident (plus_var, solver_scheme) IdentMap.empty in
            ([plus_var], `Equals (plus_var, plus_type), plus_map, Some solver_pscheme),
            (`Var ident, solver_pscheme, `Magic)
          in
          let minus_scheme =
            let minus_var = fresh_type_var ~letter:'z' () in
            let minus_type =
              type_cons_arrow type_cons_int (type_cons_arrow type_cons_int type_cons_int)
            in
            let pos = Location.none in
            let solver_scheme = new_scheme minus_var in
            let solver_pscheme = new_pscheme minus_var in
            let ident = ident "-" pos in
            let minus_map = IdentMap.add ident (minus_var, solver_scheme) IdentMap.empty in
            ([minus_var], `Equals (minus_var, minus_type), minus_map, Some solver_pscheme),
            (`Var ident, solver_pscheme, `Magic)
          in
          let mult_scheme =
            let mult_var = fresh_type_var ~letter:'z' () in
            let mult_type =
              type_cons_arrow type_cons_int (type_cons_arrow type_cons_int type_cons_int)
            in
            let pos = Location.none in
            let solver_scheme = new_scheme mult_var in
            let solver_pscheme = new_pscheme mult_var in
            let ident = ident "*" pos in
            let mult_map = IdentMap.add ident (mult_var, solver_scheme) IdentMap.empty in
            ([mult_var], `Equals (mult_var, mult_type), mult_map, Some solver_pscheme),
            (`Var ident, solver_pscheme, `Magic)
          in
          List.split [plus_scheme; minus_scheme; mult_scheme]
        in
        let default_type_decls =
          let ptyp ptyp_desc = { ptyp_desc; ptyp_loc = Location.none } in
          [
            {
              pstr_desc = Pstr_type ["list",
                { ptype_params = ["a"];
                  ptype_cstrs = [];
                  ptype_kind = Ptype_variant
                    ["[]", [], Location.none;
                     "::", [ptyp (Ptyp_var "a");
                            ptyp (Ptyp_constr (Longident.Lident "list",
                                  [ptyp (Ptyp_var "a")]));
                           ], Location.none;
                    ];
                  ptype_private = Asttypes.Public;
                  ptype_manifest = None;
                  ptype_variance = [];
                  ptype_loc = Location.none;
                }
              ];
              pstr_loc = Location.none;
            };
            {
              pstr_desc = Pstr_type ["bool",
                { ptype_params = [];
                  ptype_cstrs = [];
                  ptype_kind = Ptype_variant
                    ["true", [], Location.none;
                     "false", [], Location.none;
                    ];
                  ptype_private = Asttypes.Public;
                  ptype_manifest = None;
                  ptype_variance = [];
                  ptype_loc = Location.none;
                }
              ];
              pstr_loc = Location.none;
            };
            {
              pstr_desc = Pstr_type ["unit",
                { ptype_params = [];
                  ptype_cstrs = [];
                  ptype_kind = Ptype_variant ["()", [], Location.none];
                  ptype_private = Asttypes.Public;
                  ptype_manifest = None;
                  ptype_variance = [];
                  ptype_loc = Location.none;
                }
              ];
              pstr_loc = Location.none;
            }
          ]
        in
        if opt_default_bindings then
          let topmost_constraint, structure_items =
            generate_structure_items env (default_type_decls @ structure)
          in
          `Let (default_bindings, topmost_constraint),
          `Let (false, default_let_bindings) :: structure_items
        else
          generate_structure_items env structure

    (* This is only used by Pexp_let case. Still, it's a nice standalone block. *)
    and generate_constraint_scheme: env -> pattern * expression -> constraint_scheme =
      fun env (pat, expr) ->
        let x = fresh_type_var ~letter:'x' () in
        let { p_constraint = c1; var_map; introduced_vars; pat } =
          generate_constraint_pattern env x pat
        in
        let { e_constraint = c1'; expr } =
          generate_constraint_expression env x expr
        in
        let pscheme = new_pscheme x in
        let konstraint = `Exists (introduced_vars, `Conj (c1, c1')) in
        {
          scheme = [x], konstraint, var_map, Some pscheme;
          pat_expr = pat, pscheme, expr;
        }
    in

    (** The "driver" for OCaml constraint generation. Takes care of catching all
        errors and returning an understandable error message. *)
    try
      let e_constraint, str = generate_constraint_structure env structure in
      `Ok (e_constraint, str)
    with
      | Error e -> `Error e
      | Algebra.Core.Error e -> `Error (AlgebraError e)

end
