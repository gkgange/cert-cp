(* Registry of checkers for constraint classes. *)
module MT = MTypes
module H = Hashtbl
module C = Checker
module Sol = SolCheck

let registry = H.create 17
let sol_registry = H.create 17

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
        C.check = (fun _ _ -> false)
      }
    end

let null_sol_checker model =
  fun tokens ->
    begin
      drop_args tokens;
      {
        Sol.repr = "null-solcheck" ;
        Sol.check = (fun _ -> false)
      }
    end

let add = H.add registry
let add_sol = H.add sol_registry

(* Find the checker-constructor for the given class. *)
(*
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
*)
let find_impl tbl default warn ident =
  try
    H.find tbl ident
  with
    Not_found ->
      begin
        if !COption.verbosity > 0 then
          Format.fprintf fmt warn ident ;
        H.add tbl ident default ;
        default
      end

let find = find_impl registry null_checker "Warning: Checker not found for '%s'. Using null checker.@."
let find_sol = find_impl sol_registry null_sol_checker "Warning: Solution checker not found for '%s'.@."
