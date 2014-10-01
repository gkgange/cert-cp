(* Registry of checkers for constraint classes. *)
module H = Hashtbl

let registry = H.create 17

(* Register a new checker kind. *)
let add ident checker = H.add registry ident checker

(* Find the checker-constructor for the given class. *)
let find ident =
  try
    H.find registry ident
  with
    Not_found ->
      failwith
        (Format.sprintf "Checker not found for %s." ident )
