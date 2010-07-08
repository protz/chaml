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
%}

%token <string> IDENT
%token <string> OPERATOR
%token VAL FORALL DOT COMMA
%token QUOTE COLON
%token ARROW
%token STAR
%token RPAREN LPAREN
%token AS
%token EOL EOF

%right    ARROW                  /* core_type2 (t -> t -> t) */

%start <(string * ParserTypes.pvar) list> main
%type <string * ParserTypes.pvar> type_decl

%%

main:
| l = list(type_decl) list(EOL) EOF
  { l }

val_ident:
    IDENT                                      { $1 }
  | LPAREN OPERATOR RPAREN                      { $2 }
;

type_decl:
| VAL i = val_ident COLON list(EOL) e = core_type EOL
  { (i, e) }
| VAL i = val_ident COLON FORALL list(IDENT) DOT e = core_type EOL
  { (i, e) }

ident:
| i = IDENT
  { i }

type_longident:
| i = IDENT
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
      { match $2 with [sty] -> sty | _ -> assert false }
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
