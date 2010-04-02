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
  open Algebra
  open ParserTypes
%}

%token <string> IDENT
%token VAL INT UNIT FLOAT CHAR STRING FORALL DOT
%token QUOTE UNDERSCORE COLON
%token ARROW
%token TIMES
%token RPAREN LPAREN
%token AS
%nonassoc AS
%token EOL EOF

%right ARROW

/* Don't know why it is necessary to specify the full path here */
%start <(string * ParserTypes.pvar) list> main
%type <string * ParserTypes.pvar> type_decl
%type <ParserTypes.pvar> type_expr
%type <[`Var of string]> type_var
%type <ParserTypes.pvar> type_constr
%type <ParserTypes.pvar list> type_product
%type <ParserTypes.pvar> type_product_elt

%%

main:
| l = list(type_decl) list(EOL) EOF
  { l }

type_decl:
| VAL i = IDENT COLON e = type_expr EOL
  { (i, e) }
| VAL i = IDENT COLON FORALL list(IDENT) DOT e = type_expr EOL
  { (i, e) }

type_expr:
| v = type_var
  { (v :> ParserTypes.pvar) }
| v = type_constr
  { v }
| LPAREN e = type_expr RPAREN
  { e }
| e = type_expr AS v = type_var
  { `Alias (e, v) }
| e1 = type_expr ARROW e2 = type_expr
  { type_cons_arrow e1 e2 }
| e = type_product
  { type_cons "*" e }

type_var:
| QUOTE UNDERSCORE v = IDENT
  { `Var v }
| QUOTE v = IDENT
  { `Var v }
| v = IDENT
  { `Var v }

type_constr:
| INT
  { type_cons_int }
| CHAR
  { type_cons_char }
| STRING
  { type_cons_string }
| FLOAT
  { type_cons_float }
| UNIT
  { type_cons_unit }

type_product:
| e = type_product_elt TIMES es = type_product
  { e :: es }
| e1 = type_product_elt TIMES e2 = type_product_elt
  { [e1; e2] }

type_product_elt:
  | LPAREN e = type_expr RPAREN { e }
  | v = type_var { (v :> ParserTypes.pvar) }
  | v = type_constr { (v :> ParserTypes.pvar) }
