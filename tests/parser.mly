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
  open Typetree
%}

%token <string> IDENT
%token VAL INT UNIT FLOAT CHAR STRING
%token QUOTE UNDERSCORE COLON
%token ARROW
%token TIMES
%token RPAREN LPAREN
%token EOL EOF

%right ARROW

/* Don't know why it is necessary to specify the full path here */
%start <Typetree.type_decl list> main

%%

main:
| l = list(type_decl) EOF
  { l }

type_decl:
| VAL i = IDENT COLON e = type_expr EOL
  { (i, e) }

type_expr:
| e1 = type_expr ARROW e2 = type_expr
  { TArrow (e1, e2) }
| v = type_var
  { v }
| LPAREN e = type_expr RPAREN
  { e }
| e = type_product
  { TTuple e }

type_var:
| QUOTE UNDERSCORE v = IDENT
  { TVar v }
| QUOTE v = IDENT
  { TVar v }
| INT
  { TInt }
| CHAR
  { TChar }
| STRING
  { TString }
| FLOAT
  { TFloat }
| UNIT
  { TUnit }

type_product:
| e = type_product_elt TIMES es = type_product
  { e :: es }
| e1 = type_product_elt TIMES e2 = type_product_elt
  { [e1; e2] }

type_product_elt:
  | LPAREN e = type_expr RPAREN { e }
  | v = type_var { v }
