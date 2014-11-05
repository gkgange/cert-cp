(* Check correspondence between a model (with inferences)
 * and the initial clauses of a resolution proof. *)
module GL = Genlex
module MT = MTypes
module M = Model
module H = Hashtbl
module A = DynArray
module C = Checker

(* Look up a literal in the mapping. *)
let get_lit lmap k =
  try
    H.find lmap k
  with Not_found ->
    failwith
      (Format.sprintf "Unidentified literal identifier %d." k)

(* Convert a literal from the trace into a
 * semantic literal. *)
let tlit lmap = parser
  | [< 'GL.Kwd "-" ; 'GL.Int k >] ->
      MT.negate (get_lit lmap k)
  | [< 'GL.Int k >] ->
      if k < 0 then
        MT.negate (get_lit lmap (-k))
      else
        get_lit lmap k

(* Parse a checker hint from the trace. *)
let parse_hint =
  let haux = parser
    | [< 'GL.Kwd "-" >] -> None
    | [< 'GL.Ident ident >] -> Some ident
  in parser
  | [< 'GL.Ident "c" ; hint = haux >] -> hint

let resolve_hint model hint =
  match hint with
  | None -> None
  | Some ident ->
      Some ((M.get_checker model ident).C.check (M.get_bounds model))

(* Parse a clause from the trace. *)
let tclause lmap tokens =
  let rec aux = parser
    | [< 'GL.Int 0 >] -> []
    | [< l = (tlit lmap) ; ls = aux >] -> l :: ls
    | [< >] -> [] in
  aux tokens

(* Grab the list of antecedent clauses. *)
let rec tantecedents tokens = 
  let rec aux = parser
  | [< 'GL.Int 0 >] -> []
  | [< 'GL.Int k ; ks = aux >] -> k :: ks in
  aux tokens

let tentry lmap = parser
  | [< 'GL.Int id ; cl = tclause lmap ; ants = tantecedents >] ->
      (id, cl, ants)

let check_clause model hint tauto_check clause =
  begin
    (* Debug logging. *)
    if !COption.verbosity > 1
    then
      let fmt = Format.std_formatter in
      Format.fprintf fmt "Checking %s@."
        (M.string_of_clause model clause)
  end ;
  (* First, try looking up the clause in the table. *)
  let check = match hint with
    | None -> tauto_check
    | Some c -> c in
  if check clause then
      true
  else
    begin
      if !COption.verbosity > 0
      then
        let fmt = Format.err_formatter in
        Format.fprintf fmt "Unjustified clause: %s@."
          (M.string_of_clause model clause)
      else
        () ;
      false
    end

let check_entry model hint tauto_check (id, cl, ants) =
  match ants with
  | [] ->
      let okay = check_clause model hint tauto_check cl in
      if !COption.verbosity > 0 then
        begin
          if not okay then
            let fmt = Format.err_formatter in
            Format.fprintf fmt "Failed clause: %d@." id
        end ;
      okay
  | _ -> true

let fallback model =
  let bounds = M.get_bounds model in
  let check_with checker cl =
        let okay = checker.C.check bounds cl in
        begin
        if !COption.verbosity > 0 then
          let fmt = Format.err_formatter in
          Format.fprintf fmt "Fallback successful - %s@." checker.C.repr
        end ;
        okay
      in
  let all_checkers = M.get_all_checkers model in
  fun cl ->
      List.fold_left (fun b check -> b || check_with check cl)
      (Builtins.tauto bounds cl) all_checkers

(*
let tauto_check model = fallback model
*)
(* let tauto_check model = Builtins.tauto (M.get_bounds model) *)
let tauto_check model = Builtins.tauto_dbnd
  (Checker_impl.bounds_domset (M.get_bounds model))

let update_assumps clauses cl =
  if List.exists (fun cl_y -> Builtins.clause_subsumes cl_y cl) clauses then
    clauses
  else
    cl :: (List.filter (fun cl_y -> not (Builtins.clause_subsumes cl cl_y)) clauses)

(* Should be tail recursive; we can switch to an iterative
 * implementation if we have stack problems. *)
let rec assumptions' model hint tcheck lmap tokens assumps =
  if Stream.peek tokens = None then
    assumps
  else if Stream.peek tokens = Some (GL.Ident "c") then
    assumptions' model (resolve_hint model (parse_hint tokens))
      tcheck lmap tokens assumps
  else
    (* Get the next entry. *)
    let entry = tentry lmap tokens in
    if check_entry model hint tcheck entry then
      (* Current clause is implied by the model. *)
      assumptions' model hint tcheck lmap tokens assumps
    else
      (* Not implied; update the assumptions. *)
      let (_, cl, _) = entry in
      assumptions' model hint tcheck lmap tokens
        (update_assumps assumps cl)
    
let assumptions model lmap tokens =
  assumptions' model None (tauto_check model) lmap tokens []
