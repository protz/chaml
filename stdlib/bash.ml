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

type colors = { green: int; red: int; blue: int; }
let colors = { green = 119; red = 203; blue = 81; }

let color c fmt =
  Printf.kbprintf
    (fun buf -> Printf.sprintf "\x1b[38;5;%dm%s\x1b[0m" c (Buffer.contents buf))
    (Buffer.create 16) fmt

let underline eta =
  Printf.kprintf (Printf.sprintf "\x1b[4m%s\x1b[0m") eta

let twidth, theight =
  let height, width = ref 0, ref 0 in
  Scanf.sscanf
    (Ocamlbuild_plugin.run_and_read "stty size")
    "%d %d"
    (fun h w -> width := w; height := h);
  !width, !height

let box txt =
  let boxw = String.length txt + 4 in
  let whitespace = String.make ((twidth - boxw) / 2) ' ' in
  let charw = String.length "║" in
  let line = "═" in
  let top = String.make (charw * boxw) ' ' in
  for i = 1 to boxw - 2 do
    String.blit line 0 top (i * charw) charw;
  done;
  String.blit "╔" 0 top 0 charw;
  String.blit "╗" 0 top (charw * (boxw - 1)) charw;
  let middle = Printf.sprintf "║ %s ║" txt in
  let bottom = String.make (charw * boxw) ' ' in
  for i = 1 to boxw - 2 do
    String.blit line 0 bottom (i * charw) charw;
  done;
  String.blit "╚" 0 bottom 0 charw;
  String.blit "╝" 0 bottom (charw * (boxw - 1)) charw;
  color colors.blue "%s%s\n%s%s\n%s%s\n"
    whitespace top whitespace middle whitespace bottom
