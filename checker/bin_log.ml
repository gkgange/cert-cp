(** Binary log parser implementation. *)
module H = Hashtbl
module C_impl = Checker_impl

(* Maps proof-vars to model-vars *)
type ctx = int array

let err_fmt = Format.err_formatter

(*
let get_int ch =
  let bs = really_input_string ch 4 in
  let ks = Array.map (fun i -> String.get bs i |> int_of_char) [|0; 1; 2; 3|] in 
  (*
  for i = 0 to 3 do
    Format.fprintf err_fmt "%d@." ks.(i)
  done ;
  *)
  ks.(0) lor (ks.(1) lsl 8) lor (ks.(2) lsl 16) lor (ks.(3) lsl 24)
(*  ((ks.(0) lsl 24) lor (ks.(1) lsl 16) lor (ks.(2) lsl 8) lor ks.(3)) *)
*)


let imax = Int32.to_int Int32.max_int
let imin = Int32.to_int Int32.min_int

let ishift = imin - imax - 1

let get_int ch =
  let x_be = input_binary_int ch in
  let b0 = (x_be land 0xff) lsl 24 in
  let b1 = (x_be land 0xff00) lsl 8 in
  let b2 = (x_be land 0xff0000) lsr 8 in
  let b3 = (x_be land 0xff000000) lsr 24 in
  let x = (b0 lor b1) lor (b2 lor b3) in
  if x > imax then
    x + ishift
  else
    x

  (*
  Format.fprintf err_fmt "{%d, %d, %d, %d}@." b0 b1 b2 b3 ;
  ((b3 lsl 24) lor (b2 lsl 16))
  lor ((b1 lsl 8) lor b0)
  *)

let really_input_string ch len =
  let s = String.create len in
  really_input ch s 0 len ;
  s

let make_ctx var_tbl ch =
  (* Ignore first jump *)
  let _ = input_binary_int ch in
  let nv = get_int ch in
  (* Format.fprintf err_fmt "%d@." nv ; *)
  let vars = Array.init nv (fun i -> 0) in
  for i = 1 to nv do
    let len = get_int ch in
    let ident = really_input_string ch len in
    (* Format.fprintf err_fmt "%s@." ident ; *)
    try
      (* Format.fprintf err_fmt "%d: %s [%d]@." (i-1) ident (H.find var_tbl ident); *)
      vars.(i-1) <- H.find var_tbl ident
    with Not_found ->
      failwith (Format.sprintf "Couldn't find ident: %s" ident)
  done ;
  vars

let hint_tag = Int32.to_int Int32.max_int
let del_tag = hint_tag-1

let get_atom ctx ch =
  let var_kind = get_int ch in
  let k = get_int ch in
  let var = var_kind lsr 2 in
  (* Format.fprintf err_fmt "[%d, %d, %d, %d]@." var_kind var (var land 3) k ; *)
  let vp = match var_kind land 2 with
  | 0 -> C_impl.ILeq (ctx.(var), k)
  | _ -> C_impl.IEq (ctx.(var), k)
  in
  match var_kind land 1 with
  | 0 -> C_impl.Neg vp
  | _ -> C_impl.Pos vp

let get_atoms ctx ch =
  let rec aux sz acc =
    if sz <= 0 then
      List.rev acc
    else
      aux (sz-1) ((get_atom ctx ch) :: acc)
  in
  let sz = get_int ch in
  (* Format.fprintf err_fmt "Size: %d@." sz ; *)
  aux sz []
    
let get_ants ch =
  let rec aux sz acc =
    if sz <= 0 then
      List.rev acc
    else
      aux (sz-1) ((get_int ch) :: acc)
  in
  let sz = get_int ch in
  (* Format.fprintf err_fmt "Size: %d@." sz ; *)
  aux sz []

let next_step ctx ch =
  let tag = get_int ch in
  if tag = hint_tag then
    C_impl.Hint (get_int ch - 1)
  else if tag = del_tag then
    C_impl.Del (get_int ch)
  else
    let atoms = get_atoms ctx ch in 
    let ants = get_ants ch in
    if List.length ants = 0 then
      C_impl.Intro (tag, atoms)
    else
      C_impl.Resolve (tag, atoms, ants)

let create var_tbl ch =
  let ctx = make_ctx var_tbl ch in
  (* Stream.from (fun i -> next_step ctx ch) *)
  (fun () -> next_step ctx ch)
