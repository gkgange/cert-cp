(* Check correspondence between a model (with inferences)
 * and the initial clauses of a resolution proof. *)
module GL = Genlex
module MT = MTypes
module M = Model
module H = Hashtbl
module A = DynArray
module C = Checker

(* Map integers to literals.
 * Should add an option for a separate mapping. *)
let lmap_of_model model =
  let lmap = H.create 3037 in
  M.lits_iteri (fun i _ lit -> H.add lmap (3+i) lit) model ;
  lmap

(* Hash-table of pre-checked clauses. *)
let clause_table clauses =
  let ctable = H.create 11437 in
  List.iter (fun cl -> H.add ctable (List.sort compare cl) ()) clauses ;
  ctable
  
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

let check_clause model tauto_check cltable clause =
  begin
    (* Debug logging. *)
    if !COption.verbosity > 1
    then
      let fmt = Format.std_formatter in
      Format.fprintf fmt "Checking %s@."
        (M.string_of_clause model clause)
  end ;
  (* First, try looking up the clause in the table. *)
  try
    let _ = H.find cltable (List.sort compare clause) in
    true
  with Not_found ->
    (* Otherwise, check if it's a tautology (under the
     * model semantics). *)
    if tauto_check clause then
      true
    else
      begin
        if !COption.verbosity > 0
        then
          let fmt = Format.err_formatter in
          Format.fprintf fmt "Failure - unjustified clause: %s@."
            (M.string_of_clause model clause)
        else
          () ;
        false
      end

let check_entry model tauto_check cltable (id, cl, ants) =
  match ants with
  | [] ->
      let okay = check_clause model tauto_check cltable cl in
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
let tauto_check model = Builtins.tauto (M.get_bounds model)

let check model clauses tokens =
  let lmap = lmap_of_model model
  and ctable = clause_table clauses in
  let okay = ref true in
  while Stream.peek tokens <> None
  do
    (* Get the next entry. *)
    let entry = tentry lmap tokens in
    (* check_entry model tauto_check ctable entry && check_aux tokens *)
    okay := check_entry model (tauto_check model) ctable entry && !okay
  done ;
  !okay

let update_assumps clauses cl =
  if List.exists (fun cl_y -> Builtins.clause_subsumes cl_y cl) clauses then
    clauses
  else
    cl :: (List.filter (fun cl_y -> not (Builtins.clause_subsumes cl cl_y)) clauses)

(* Should be tail recursive; we can switch to an iterative
 * implementation if we have stack problems. *)
let rec assumptions' model tcheck ctable lmap tokens assumps =
  if Stream.peek tokens = None then
    assumps
  else
    (* Get the next entry. *)
    let entry = tentry lmap tokens in
    if check_entry model tcheck ctable entry then
      (* Current clause is implied by the model. *)
      assumptions' model tcheck ctable lmap tokens assumps
    else
      (* Not implied; update the assumptions. *)
      let (_, cl, _) = entry in
      assumptions' model tcheck ctable lmap tokens
        (update_assumps assumps cl)
    
let assumptions model clauses tokens =
  let lmap = lmap_of_model model
  and ctable = clause_table clauses in
  assumptions' model (tauto_check model) ctable lmap tokens []
