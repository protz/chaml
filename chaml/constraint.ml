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

module Make (S: Algebra.SOLVER) = struct

  open Algebra.TypeCons
  open Algebra.Identifiers
  open Algebra.Core

  type type_scheme =
      S.var type_var list
    * type_constraint
    * (S.var type_var * S.scheme) IdentMap.t

  and type_constraint = [
      `True
    | `Done
    | `Conj of type_constraint * type_constraint
    | `Exists of S.var type_var list * type_constraint
    | `Equals of S.var type_var * S.var type_term
    | `Instance of ident * S.var type_var * S.instance
    | `Let of type_scheme list * type_constraint
  ]


  (* The polymorphic variants allow us to make a difference between simply a
   * variable and a more general term. But we need to do the casts ourselves. *)
  let tv_tt x = (x: 'a type_var :> 'a type_term)
  let tvl_ttl x = (x: 'a type_var list :> 'a type_term list)


  module PrettyPrinter = struct
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
      | _ :: tl -> { pp_env with color_stack = tl }
      | [] -> pp_env

    let pp_env_brack pp_env s = match pp_env.color_stack with
      | hd :: _ when pp_env.pretty_printing ->
          String.concat "" [Bash.color hd "["; s; Bash.color hd "]"]
      | _ ->
          Printf.sprintf "[%s]" s

    let pp_env_paren pp_env s = match pp_env.color_stack with
      | hd :: _ when pp_env.pretty_printing ->
          String.concat "" [Bash.color hd "("; s; Bash.color hd ")"]
      | _ ->
          Printf.sprintf "(%s)" s

    let string_of_type_var = function
      | `Var s -> (S.string_of_var s)

    let string_of_constraint
        ~pretty_printing:opt_pretty_printing
        (konstraint: type_constraint) =
      let inc i = " " ^ i in
      let space_before_type_var = fun x -> " " ^ (string_of_type_var x) in
      let rec string_of_constraint pp_env = fun i -> function
        | `True ->
            "true"
        | `Done ->
            "dump"
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
            let t1 = string_of_type_var t1 in
            let t2 = string_of_type pp_env t2 in
            String.concat "" [t1; " = "; t2]
        | `Instance (x, t, _) ->
            let x = string_of_ident x in
            let t = string_of_type_var t in
            String.concat "" [x; " < "; t]
        | `Let (schemes, c) ->
            let i' = inc i in
            let sep = ";\n" ^ i' in
            let schemes = String.concat sep (List.map (string_of_type_scheme pp_env i') schemes) in
            let c = string_of_constraint pp_env i c in
            String.concat "" ("let\n" :: i' :: schemes :: ["\n"; i; "in\n"; i; c])
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
          (fun i (v, _) ->
            l := (String.concat " : " [string_of_ident i; string_of_type_var v]) :: !l)
          var_map;
        Buf.add buf (String.concat "; " !l);
        pp_env_paren pp_env (Buf.flush buf)
      and string_of_type pp_env =
        function
        | `Var _ as v -> string_of_type_var v
        | `Cons ({ cons_name; _ }, types) ->
           match cons_name with
           | "->" as op ->
               let t1 = string_of_type pp_env (List.nth types 0) in
               let t2 = string_of_type pp_env (List.nth types 1) in
               String.concat " " [t1; op; t2]
           | "*" ->
               let sub_types = List.map (string_of_type pp_env) types in
               String.concat " * " sub_types
           | _ as op ->
               (* Will probably need something more elaborate here once we get data
                * types *)
               let types = List.map (string_of_type pp_env) types in
               let types = if List.length types > 0 then
                 pp_env_paren pp_env (String.concat ", " types)
               else
                 ""
               in
               String.concat "" [op; types]
      in
      let pp_env = fresh_pp_env ~pretty_printing:opt_pretty_printing () in
      (* Because of the value restrictiooooooooooon *)
      string_of_constraint pp_env "" konstraint
  end
end
