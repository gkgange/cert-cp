(* Top-level checker code. *)
module List = ExtLib.List
module L = List
module GL = Genlex
module MT = MTypes
module C = Checker
module M = Model
module S = Spec
module P = Parse

module DL = Dynlink

(* constraint(id) |- clause *)
type inference = (MT.ident * MT.clause)

let fmt = Format.std_formatter
let err_fmt = Format.err_formatter

let log_failure model checker cl =
  Format.fprintf fmt "Inference failed: %s |- %s.@."
    (checker.C.repr) (M.string_of_clause model cl)

let log info args =
  Format.fprintf fmt info args ; Format.fprintf fmt "@."

let string_of_assumptions model clauses =
  let rec aux clauses =
    match clauses with
    | [] -> ""
    | [cl] -> M.string_of_clause model cl
    | (cl :: cls) -> (M.string_of_clause model cl) ^ "," ^ (aux cls)
  in
  "{" ^ (aux clauses) ^ "}"


(* Find the checker corresponding to a specified
 * constraint name, call it on the given clause. *)
let check_inference model bounds ident clause =
  try
    let checker = M.get_checker model ident in
    let okay = checker.C.check bounds clause in
    if !COption.verbosity > 0 && not okay then
      log_failure model checker clause ;
    if !COption.verbosity > 1 && okay then
      Format.fprintf fmt "Inference okay: %s |- %s.@."
        (checker.C.repr) (M.string_of_clause model clause) ;
    okay
  with Not_found ->
    begin
      log "Error: constraint not found: %s" ident ;
      false
    end

(* Check a set of inferences; terminates after the
 * first failure. *)
(*
let check_inferences model bounds infs =
  L.fold_left (fun b (id, cl) -> b && check_inference model bounds id cl) true infs
  *)

let check_inferences model bounds infs =
  L.fold_left (fun b (id, cl) -> check_inference model bounds id cl && b) true infs
  
(* Parsing code for definitions. *)
let parse_defn spec = parser
  | [< 'GL.Ident id ; 'GL.Kwd ":=" ; v = spec id >] -> v

(* Determining the value of an identifier. *)
let term_defn model id =
  let aux key = match key with
  | "int" ->
     begin parser
       | [< 'GL.Int l ; 'GL.Int u >] -> M.add_ivar model id (Some (l,u))
       | [< >] -> M.add_ivar model id None
     end
  | "bool" ->
      begin parser
        | [< >] -> M.add_bvar model id
      end
  | "prop" ->
      begin parser
        | [< prop = P.parse_vprop model >] ->
            M.add_lit model id prop
      end
  | _ ->
    let pcon = (Registry.find key) model in
    fun tokens ->
      (* Indirection is to support (eventually) providing
       * multiple checkers for a constraint. *)
      let args = P.grab_args tokens in
      M.add_checker model id (pcon (Stream.of_list args))
    in
  parser
    | [< 'GL.Ident key ; v = aux key >] -> v

(*
let parse_clause model =
  let parse_lit = parser
    | [< 'GL.Kwd "~" ; 'GL.Ident id >] ->
        MT.Neg (M.get_vprop model id)
    | [< 'GL.Ident id >] ->
        MT.Pos (M.get_vprop model id)
  in S.listof parse_lit
  *)

let chomp tokens token =
  let next = Stream.next tokens in
  if next <> token then
    failwith "Parse error."

let parse_model tokens =
  let model = M.create () in
  chomp tokens (GL.Kwd "[") ;
  if Stream.peek tokens <> (Some (GL.Kwd "]")) then
    begin
      parse_defn (term_defn model) tokens ;
      while Stream.peek tokens = Some (GL.Kwd ",") 
      do
        Stream.junk tokens ;
        parse_defn (term_defn model) tokens 
      done
    end ;
  chomp tokens (GL.Kwd "]") ;
  model

  (*
  parser
    | [< _ = S.listof (parse_defn (term_defn model)) >] -> model
    (*
  let aux = parser
    | [< 'GL.Ident id ; 'GL.Kwd ":=" ; _ = (term_defn model id) >] -> ()
    | [< >] -> ()
  in parser
    | [< 'GL.Kwd "[" ; _ = aux ; 'GL.Kwd "]" >] -> model
    *)
    *)

  (*
let parse_inferences model =
  let parse_inf = parser
    | [< 'GL.Ident id ; 'GL.Kwd "|-" ; cl = P.parse_clause model >] -> (id, cl)
  in let rec aux = parser
    | [< inf = parse_inf ; tail = aux >] -> inf :: tail
    | [< >] -> []
  in aux
  *)

let parse_inf model = parser
  | [< 'GL.Ident id ; 'GL.Kwd "|-" ; cl = P.parse_clause model >] -> (id, cl)

let parse_inferences model tokens =
  let rec aux tl tokens =
    match Stream.peek tokens with
    | None -> List.rev tl
    | _ -> aux ((parse_inf model tokens) :: tl) tokens
  in aux [] tokens

(*
let parse_inferences = parser
  | [< 'Ident id ; 'Kwd "|-" ; cl = (S.listof parse_lit) >] ->
      (id, M.clause_of_model)
*)

let rec parse_and_check_inferences model bounds tokens =
  match Stream.peek tokens with
  | None -> true
  | _ -> 
     let (id, cl) = parse_inf model tokens in
     if check_inference model bounds id cl then
       parse_and_check_inferences model bounds tokens
     else
       false

let check_corresp model clauses =
  match !COption.tracefile with
  | None -> true
  | Some tfile ->
      let tchannel = open_in tfile in
      let ttoks = Spec.lexer (Stream.of_channel tchannel) in
      Corresp.check model clauses ttoks

let get_assumptions model clauses =
  match !COption.tracefile with
  | None -> None
  | Some tfile ->
      let tchannel = open_in tfile in
      let ttoks = Spec.lexer (Stream.of_channel tchannel) in
      Some (Corresp.assumptions model clauses ttoks)


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
  Builtins.register ();
  List.iter (fun m -> DL.loadfile_private m) !COption.modules ;
  let tokens = Spec.lexer (Stream.of_channel input) in 
  let model = parse_model tokens in
  (*
  let okay =
    if !COption.stream then
      parse_and_check_inferences model (M.get_bounds model) tokens
    else
      let infs = parse_inferences model tokens in
      check_inferences model (M.get_bounds model) infs
        && check_corresp model (L.map (fun (i, cl) -> cl) infs)
    in
  if okay then
    Format.fprintf fmt "OKAY@."
  else
    Format.fprintf fmt "FAILURE: invalid inference found.@." 
    *)
  let infs = parse_inferences model tokens in
  if check_inferences model (M.get_bounds model) infs
  then
    let assumps =
      get_assumptions model (L.map (fun (i, cl) -> cl) infs) in
    match assumps with
    | None -> Format.fprintf fmt "OKAY (no trace)@."
    | Some [] -> Format.fprintf fmt "OKAY@."
    | Some xs ->
        Format.fprintf fmt "ASSUMPTIONS %s@."
          (string_of_assumptions model xs)
  else
    Format.fprintf fmt "FAILURE: invalid clause logged.@."
      
let _ = main () 