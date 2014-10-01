(* Registry of checkers for constraint classes. *)
module H = Hashtbl
module C = Checker

let registry = H.create 17

let fmt = Format.std_formatter
let err_fmt = Format.err_formatter

let rec drop_args tokens =
  match (Stream.peek tokens) with
  | None -> ()
  | Some (Genlex.Kwd ")") -> ()
  | _ -> (Stream.junk tokens ; drop_args tokens)

let null_checker model =
  fun tokens ->
    begin
      drop_args tokens;
      {
        C.repr = "null-checker" ;
        C.check = (fun cl -> false)
      }
    end

(* Register a new checker kind. *)
let add ident checker = H.add registry ident checker

(* Find the checker-constructor for the given class. *)
let find ident =
  try
    H.find registry ident
  with
    Not_found ->
      begin
        if !COption.verbosity > 0 then
          Format.fprintf fmt "WARNING: Checker not found for '%s'. Using null checker.@." ident ;
        add ident null_checker ;
        null_checker
      end

