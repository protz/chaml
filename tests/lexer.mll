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

{
  open Parser
  exception LexingError of string

  let keywords =
    let t = Hashtbl.create 8 in
      List.iter
        (fun (keyword, token) -> Hashtbl.add t keyword token)
        [
          "val", VAL;
          "as", AS;
          "type", TYPE;
          "and", AND;
          "private", PRIVATE;
          "of", OF;
          "mutable", MUTABLE;
        ];
      t

  let filter lexbuf =
    let ident = Lexing.lexeme lexbuf in
    match Jhashtbl.find_opt keywords ident with
    | Some kw -> kw
    | None ->
        LIDENT (ident)

}

let lowercase = [ 'a'-'z' ]
let uppercase = [ 'A'-'Z' ]
let whitespace = [ ' ' '\t' ]
let number = [ '0'-'9' ]

let identchar =
  ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']

rule token = parse
| '\n'
  { EOL }

| '\'' | '\'' '_'
  { QUOTE }

| '*'
  { STAR }

| '-'
  { MINUS }

| '='
  { EQUAL }

| '('
  { LPAREN }

| ')'
  { RPAREN }

| '-' '>'
  { ARROW }

| ':'
  { COLON }

| ':' ':'
  { COLONCOLON }

| ';'
  { SEMI }

| ','
  { COMMA }

| '{'
  { LBRACE }

| '}'
  { RBRACE }

| '|'
  { BAR }

| '.'
  { DOT }

| lowercase identchar*
  { filter lexbuf }

| uppercase identchar*
  { UIDENT (Lexing.lexeme lexbuf) }

| '@'
  { OPERATOR ("@") }

| whitespace
  { token lexbuf }

| eof
  { EOF }

| _
  {
    raise (LexingError (Printf.sprintf
                          "At offset %d: unexpected character %s\n"
                          (Lexing.lexeme_start lexbuf)
                          (Lexing.lexeme lexbuf)))
  }
