/*****************************************************************************/
/*  ChaML, a type-checker that uses constraints and a kernel language        */
/*  Copyright (C) 2010 Jonathan Protzenko                                    */
/*                                                                           */
/*  This program is free software: you can redistribute it and/or modify     */
/*  it under the terms of the GNU General Public License as published by     */
/*  the Free Software Foundation, either version 3 of the License, or        */
/*  (at your option) any later version.                                      */
/*                                                                           */
/*  This program is distributed in the hope that it will be useful,          */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of           */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            */
/*  GNU General Public License for more details.                             */
/*                                                                           */
/*  You should have received a copy of the GNU General Public License        */
/*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    */
/*                                                                           */
/*****************************************************************************/

%{
  open ParserTypes
  open Algebra.TypeCons

  let type_cons cons_name args =
    `Cons ({ cons_name; cons_arity = List.length args }, args)

  (* Remove this as soon as we have a representation for type decls.
   * Warning: we do not parse type decls, we just ignore them, but the right
   * rules have been copied from the OCaml parser. We don't print them either in
   * ChaML anyway.*)
  open Location
  open Parsetree
  open Asttypes
  let mktyp d =
    { ptyp_desc = d; ptyp_loc = symbol_rloc() }

  exception Not_implemented
%}

%token <string> LIDENT
%token <string> UIDENT
%token <string> OPERATOR
%token VAL FORALL DOT COMMA
%token QUOTE COLON
%token ARROW BAR PRIVATE PLUS SEMI
%token STAR MINUS MUTABLE TYPE
%token RPAREN LPAREN COLONCOLON EQUAL
%token AS AND LBRACE RBRACE OF
%token EOL EOF

%right    ARROW                  /* core_type2 (t -> t -> t) */

%start <(string * ParserTypes.pvar) list> main
%type <(string * ParserTypes.pvar) list> type_decl

%%

main:
| l = list(type_decl) list(EOL) EOF
  { List.flatten l }

val_ident:
    LIDENT                                      { $1 }
  | LPAREN OPERATOR RPAREN                      { $2 }
;

type_decl:
| VAL i = val_ident COLON list(EOL) e = core_type EOL
  { [i, e] }
| VAL i = val_ident COLON FORALL list(LIDENT) DOT e = core_type EOL
  { [i, e] }
| TYPE type_declarations EOL
  { try [] with Not_implemented -> [] }

ident:
| i = LIDENT
  { i }

type_longident:
| i = LIDENT
  { i }

core_type:
    t = core_type2
      { t }
  | t = core_type2 AS QUOTE i = ident
      { `Alias (t, `Var i) }
;
core_type2:
    simple_core_type_or_tuple
      { $1 }
  | core_type2 ARROW core_type2
      { type_cons_arrow $1 $3 }
;

simple_core_type:
    simple_core_type2
      { $1 }
  | LPAREN core_type_comma_list RPAREN
      { match $2 with [sty] -> sty | _ -> raise Not_implemented }
;
simple_core_type2:
    QUOTE ident
      { `Var $2 }
  | type_longident
      { type_cons $1 [] }
  | simple_core_type2 type_longident
      { type_cons $2 [$1] }
  | LPAREN core_type_comma_list RPAREN type_longident
      { type_cons $4 (List.rev $2) }
;

simple_core_type_or_tuple:
    simple_core_type                            { $1 }
  | simple_core_type STAR core_type_list
      { type_cons_tuple ($1 :: List.rev $3) }
;

core_type_comma_list:
    core_type                                   { [$1] }
  | core_type_comma_list COMMA core_type        { $3 :: $1 }
;

core_type_list:
    simple_core_type                            { [$1] }
  | core_type_list STAR simple_core_type        { $3 :: $1 }
;

/* TYPE DECLARATIONS */

type_declarations:
    type_declaration                            { [$1] }
  | type_declarations AND type_declaration      { $3 :: $1 }
;

type_declaration:
    type_parameters LIDENT type_kind
      { }
;

type_kind:
    /*empty*/
      { (Ptype_abstract, Public, None) }
  | EQUAL core_type
      { (Ptype_abstract, Public, Some $2) }
  | EQUAL PRIVATE core_type
      { (Ptype_abstract, Private, Some $3) }
  | EQUAL constructor_declarations
      { (Ptype_variant(List.rev $2), Public, None) }
  | EQUAL PRIVATE constructor_declarations
      { (Ptype_variant(List.rev $3), Private, None) }
  | EQUAL private_flag BAR constructor_declarations
      { (Ptype_variant(List.rev $4), $2, None) }
  | EQUAL private_flag LBRACE label_declarations option(SEMI) RBRACE
      { (Ptype_record(List.rev $4), $2, None) }
  | EQUAL core_type EQUAL private_flag option(BAR) constructor_declarations
      { (Ptype_variant(List.rev $6), $4, Some $2) }
  | EQUAL core_type EQUAL private_flag LBRACE label_declarations option(SEMI) RBRACE
      { (Ptype_record(List.rev $6), $4, Some $2) }
;
type_parameters:
    /*empty*/                                   { [] }
  | type_parameter                              { [$1] }
  | LPAREN type_parameter_list RPAREN           { List.rev $2 }
;
type_parameter:
    type_variance QUOTE ident                   { $3, $1 }
;
type_variance:
    /* empty */                                 { false, false }
  | PLUS                                        { true, false }
  | MINUS                                       { false, true }
;
type_parameter_list:
    type_parameter                              { [$1] }
  | type_parameter_list COMMA type_parameter    { $3 :: $1 }
;
constructor_declarations:
    constructor_declaration                     { [$1] }
  | constructor_declarations BAR constructor_declaration { $3 :: $1 }
;
constructor_declaration:
    constr_ident constructor_arguments          { ($1, $2, symbol_rloc()) }
;
constructor_arguments:
    /*empty*/                                   { [] }
  | OF core_type_list                           { [] }
;
label_declarations:
    label_declaration                           { [$1] }
  | label_declarations SEMI label_declaration   { $3 :: $1 }
;
label_declaration:
    mutable_flag LIDENT COLON poly_type          { ($2, $1, $4, symbol_rloc()) }
;

constr_ident:
    UIDENT                                      { $1 }
/*  | LBRACKET RBRACKET                           { "[]" } */
/*  | LPAREN RPAREN                               { "()" } */
  | COLONCOLON                                  { "::" }
/*  | LPAREN COLONCOLON RPAREN                    { "::" } */
/*  | FALSE                                       { "false" }
  | TRUE                                        { "true" } */
;

mutable_flag:
    /* empty */                                 { Immutable }
  | MUTABLE                                     { Mutable }
;

/* Polymorphic types */

typevar_list:
        QUOTE ident                             { [$2] }
      | typevar_list QUOTE ident                { $3 :: $1 }
;
poly_type:
        core_type
          { raise Not_implemented }
      | typevar_list DOT core_type
          { raise Not_implemented }
;

private_flag:
    /* empty */                                 { Public }
  | PRIVATE                                     { Private }
;
