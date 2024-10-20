(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Xml_datatype

exception Marshal_error of string * xml

(** Utility functions *)

let rec get_attr attr = function
  | [] -> raise Not_found
  | (k, v) :: l when CString.equal k attr -> v
  | _ :: l -> get_attr attr l

let massoc x l =
  try get_attr x l
  with Not_found -> raise (Marshal_error("attribute " ^ x,PCData "not there"))

let constructor t c args = Element (t, ["val", c], args)
let do_match t mf = function
  | Element (s, attrs, args) when CString.equal s t ->
      let c = massoc "val" attrs in
      mf c args
  | x -> raise (Marshal_error (t,x))

let singleton = function
  | [x] -> x
  | l -> raise (Marshal_error
      ("singleton",PCData ("list of length " ^ string_of_int (List.length l))))

let empty = function
  | [] -> ()
  | l -> raise (Marshal_error
      ("empty",PCData ("list of length " ^ string_of_int (List.length l))))

let raw_string = function
  | [] -> ""
  | [PCData s] -> s
  | x::_ -> raise (Marshal_error("raw string",x))

(** Base types *)

let of_unit () = Element ("unit", [], [])
let to_unit : xml -> unit = function
  | Element ("unit", [], []) -> ()
  | x -> raise (Marshal_error ("unit",x))

let of_bool (b : bool) : xml =
  if b then constructor "bool" "true" []
  else constructor "bool" "false" []
let to_bool : xml -> bool = do_match "bool" (fun s _ -> match s with
  | "true" -> true
  | "false" -> false
  | x -> raise (Marshal_error("bool",PCData x)))

let of_list (f : 'a -> xml) (l : 'a list) =
  Element ("list", [], List.map f l)
let to_list (f : xml -> 'a) : xml -> 'a list = function
  | Element ("list", [], l) -> List.map f l
  | x -> raise (Marshal_error("list",x))

let of_option (f : 'a -> xml) : 'a option -> xml = function
  | None -> Element ("option", ["val", "none"], [])
  | Some x -> Element ("option", ["val", "some"], [f x])
let to_option (f : xml -> 'a) : xml -> 'a option = function
  | Element ("option", ["val", "none"], []) -> None
  | Element ("option", ["val", "some"], [x]) -> Some (f x)
  | x -> raise (Marshal_error("option",x))

let of_string (s : string) : xml = Element ("string", [], [PCData s])
let to_string : xml -> string = function
  | Element ("string", [], l) -> raw_string l
  | x -> raise (Marshal_error("string",x))

let of_int (i : int) : xml = Element ("int", [], [PCData (string_of_int i)])
let to_int : xml -> int = function
  | Element ("int", [], [PCData s]) ->
    (try int_of_string s with Failure _ -> raise(Marshal_error("int",PCData s)))
  | x -> raise (Marshal_error("int",x))

let of_pair (f : 'a -> xml) (g : 'b -> xml) (x : 'a * 'b) : xml =
  Element ("pair", [], [f (fst x); g (snd x)])
let to_pair (f : xml -> 'a) (g : xml -> 'b) : xml -> 'a * 'b = function
  | Element ("pair", [], [x; y]) -> (f x, g y)
  | x -> raise (Marshal_error("pair",x))

let of_union (f : 'a -> xml) (g : 'b -> xml) : ('a,'b) CSig.union -> xml = function
  | CSig.Inl x -> Element ("union", ["val","in_l"], [f x])
  | CSig.Inr x -> Element ("union", ["val","in_r"], [g x])
let to_union (f : xml -> 'a) (g : xml -> 'b) : xml -> ('a,'b) CSig.union = function
  | Element ("union", ["val","in_l"], [x]) -> CSig.Inl (f x)
  | Element ("union", ["val","in_r"], [x]) -> CSig.Inr (g x)
  | x -> raise (Marshal_error("union",x))

(** More elaborate types *)

let of_edit_id i = Element ("edit_id",["val",string_of_int i],[])
let to_edit_id = function
  | Element ("edit_id",["val",i],[]) ->
      let id = int_of_string i in
      assert (id <= 0 );
      id
  | x -> raise (Marshal_error("edit_id",x))

let of_loc loc =
  let {
    Loc.fname
  ; line_nb
  ; bol_pos
  ; line_nb_last
  ; bol_pos_last
  ; bp
  ; ep
  } = loc in
  let fname = match fname with
  | ToplevelInput -> []
  | InFile { dirpath = None; file } -> [ ("file", file) ]
  | InFile { dirpath = Some dir; file } -> [ ("dirpath", dir); ("file", file) ] in
  Element ("loc",
           fname @
           [ ("line_nb", string_of_int line_nb)
           ; ("bol_pos", string_of_int bol_pos)
           ; ("line_nb_last", string_of_int line_nb_last)
           ; ("bol_pos_last", string_of_int bol_pos_last)
           ; ("start", string_of_int bp)
           ; ("stop", string_of_int ep )
           ],
           [])

let to_loc xml =
  match xml with
  | Element ("loc", l,[]) as x ->
    (try
       let fname =
         let dirpath = try Some (get_attr "dirpath" l) with Not_found -> None in
         let file = try Some (get_attr "file" l) with Not_found -> None in
         match dirpath, file with
         | None, None -> Loc.ToplevelInput
         | dirpath, Some file -> Loc.InFile { dirpath; file }
         | Some _, None -> raise (Marshal_error("loc",x)) in
       let line_nb = massoc "line_nb" l |> int_of_string in
       let bol_pos = massoc "bol_pos" l |> int_of_string in
       let line_nb_last = massoc "line_nb_last" l |> int_of_string in
       let bol_pos_last = massoc "bol_pos_last" l |> int_of_string in
       let bp = massoc "start" l |> int_of_string in
       let ep = massoc "stop" l |> int_of_string in
       { Loc.fname
       ; line_nb
       ; bol_pos
       ; line_nb_last
       ; bol_pos_last
       ; bp
       ; ep }
     with Not_found | Invalid_argument _ ->
       raise (Marshal_error("loc",x)))
  | x -> raise (Marshal_error("loc",x))

let of_xml x = Element ("xml", [], [x])
let to_xml xml = match xml with
| Element ("xml", [], [x]) -> x
| x -> raise (Marshal_error("xml",x))
