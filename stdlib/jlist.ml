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

let rec split3 = function
  | (x, y, z) :: l ->
      let l1, l2, l3 = split3 l in
      (x :: l1, y :: l2, z :: l3)
  | [] ->
      [], [], []

let ignore_map f l =
  ignore (List.map (fun x -> ignore (f x)) l)

let iteri f l =
  let rec iteri i f = function
    | [] -> ()
    | e :: rest -> f i e; iteri (i + 1) f rest
  in
  iteri 0 f l

let iter2i f l l' =
  let rec iter2i i f l l' = match l, l' with
    | ([], []) -> ()
    | (e :: rest, e' :: rest') -> f i e e'; iter2i (i + 1) f rest rest'
    | _ -> failwith "iter2i: lengths do not match"
  in
  iter2i 0 f l l'

let rec append_rev_front x y = match x,y with
  | [], l ->
      l
  | x::xs, l ->
      append_rev_front xs (x :: l)

(* Removes duplicates from a list. The default behaviour is to remove identical
 * elements. You can provide your own equality function (and possibly a better
 * hash function) to optimize things or compare elements using a custom
 * criterion. *)
let remove_duplicates (type t') ?(hash_func=Hashtbl.hash) ?(equal_func=(=)) (l: t' list) =
  let module S = struct
    type t = t'
    let equal = equal_func
    let hash = hash_func
  end in
  let module MHT = Hashtbl.Make(S) in
  let seen = MHT.create 16 in
  let l' = ref [] in
  List.iter
    (fun x ->
       if not (MHT.mem seen x) then begin MHT.add seen x (); l' := x :: !l' end
    )
    l;
  !l'

let max l = List.fold_left max min_int l

let filter_some l =
  let l = List.filter (fun x -> x <> None) l in
  List.map Option.extract l

let make i elt =
  let rec make acc i =
    if i > 0 then
      make (elt :: acc) (i - 1)
    else
      acc
  in
  make [] i
