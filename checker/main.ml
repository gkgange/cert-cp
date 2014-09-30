(* Top-level checker code. *)
module List = ExtLib.List
module L = List
module GL = Genlex
module MT = MTypes
module C = Checker
module M = Model
module S = Spec

module DL = Dynlink

(* constraint(id) |- clause *)
type inference = (MT.ident * MT.clause)

let fmt = Format.std_formatter
let err_fmt = Format.err_formatter

let log_failure checker _ =
  Format.fprintf fmt "Inference failed: %s |- {{FIXME}}."
    (checker.C.repr) (* (MT.string_of_clause clause) *)

let log info args =
  Format.fprintf fmt info args ; Format.fprintf fmt "@."

let check_inference model ident clause =
  try
    let checker = M.get_checker model ident in
    let okay = checker.C.check clause in
    if !COption.verbosity > 0 && not okay then
      log_failure checker clause ;
    okay
  with Not_found ->
    begin
      log "Error: constraint not found: %s" ident ;
      false
    end

let check_inferences model infs =
  L.fold_left (fun b (id, cl) -> b && check_inference model id cl) true infs
  
let parse_defn spec = parser
  | [< 'GL.Ident id ; 'GL.Kwd ":=" ; v = spec id >] -> v

let term_defn model id =
  let aux key = match key with
  | "int" ->
     begin parser
       | [< >] -> M.add_ivar model id
     end
  | "bool" ->
      begin parser
        | [< >] -> M.add_bvar model id
      end
  | _ -> let pcon = Registry.find key in
    begin parser
      | [< 'GL.Kwd "(" ; checker = pcon ; 'GL.Kwd ")" >] ->
          M.add_checker model id checker
    end in
  parser
    | [< 'GL.Ident key ; v = aux key >] -> v

let parse_clause model =
  let parse_lit = parser
    | [< 'GL.Kwd "~" ; 'GL.Ident id >] ->
        MT.Neg (M.get_vprop model id)
    | [< 'GL.Ident id >] ->
        MT.Pos (M.get_vprop model id)
  in S.listof parse_lit

let parse_model =
  let model = M.create () in
  parser
    | [< _ = S.listof (parse_defn (term_defn model)) >] -> model
    (*
  let aux = parser
    | [< 'GL.Ident id ; 'GL.Kwd ":=" ; _ = (term_defn model id) >] -> ()
    | [< >] -> ()
  in parser
    | [< 'GL.Kwd "[" ; _ = aux ; 'GL.Kwd "]" >] -> model
    *)


let parse_inferences model =
  let parse_inf = parser
    | [< 'GL.Ident id ; 'GL.Kwd "|-" ; cl = parse_clause model >] -> (id, cl)
  in let rec aux = parser
    | [< inf = parse_inf ; tail = aux >] -> inf :: tail
    | [< >] -> []
  in aux
(*
let parse_inferences = parser
  | [< 'Ident id ; 'Kwd "|-" ; cl = (S.listof parse_lit) >] ->
      (id, M.clause_of_model)
*)

let main () =
  (* Parse the command-line arguments *)
  Arg.parse
    COption.speclist
      (begin fun infile -> COption.infile := Some infile end)
      "cp-certify <options> <inputfile>"
  ;
  (* Parse the program *)
  let input = match !COption.infile with
      | None -> stdin
      | Some file -> open_in file
  in
  (* Register any additional checker modules. *)
  List.iter (fun m -> DL.loadfile_private m) !COption.modules ;
  let tokens = Spec.lexer (Stream.of_channel input) in 
  let model = parse_model tokens in
  let infs = parse_inferences model tokens in
  let okay = check_inferences model infs in
  if okay then
    Format.fprintf fmt "OKAY@."
  else
    Format.fprintf fmt "FAILURE: invalid inference found.@." 

let _ = main () 
