(* Check correspondence between a model (with inferences)
 * and the initial clauses of a resolution proof. *)
module GL = Genlex
module MT = MTypes
module M = Model
module H = Hashtbl
module A = DynArray
module C = Checker

let lmap_of_model model =
  let lmap = H.create 3037 in
  M.lits_iteri (fun i _ lit -> H.add lmap (3+i) lit) model ;
  lmap

let clause_table clauses =
  let ctable = H.create 11437 in
  List.iter (fun cl -> H.add ctable (List.sort compare cl) ()) clauses ;
  ctable
  
let get_lit lmap k =
  try
    H.find lmap k
  with Not_found ->
    failwith
      (Format.sprintf "Unidentified literal identifier %d." k)

let tlit lmap = parser
  | [< 'GL.Kwd "-" ; 'GL.Int k >] ->
      MT.negate (get_lit lmap k)
  | [< 'GL.Int k >] ->
      if k < 0 then
        MT.negate (get_lit lmap (-k))
      else
        get_lit lmap k


let tclause lmap tokens =
  let rec aux = parser
    | [< 'GL.Int 0 >] -> []
    | [< l = (tlit lmap) ; ls = aux >] -> l :: ls
    | [< >] -> [] in
  aux tokens

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
    if !COption.verbosity > 1
    then
      let fmt = Format.std_formatter in
      Format.fprintf fmt "Checking %s@."
        (M.string_of_clause model clause)
  end ;
  try
    let _ = H.find cltable (List.sort compare clause) in
    true
  with Not_found ->
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

let check model clauses tokens =
  let lmap = lmap_of_model model
  and ctable = clause_table clauses in
  (* *)
  let bounds = M.get_bounds model in
  let tauto_check = Builtins.tauto bounds in
  (*
  let tauto_check = fallback model in
  *)
  let rec check_aux tokens =
    match Stream.peek tokens with
    | None ->
      (* Checked all entries in the resolution proof. *)
      true
    | _ ->
      (* Get the next entry. *)
      let entry = tentry lmap tokens in
      (* check_entry model tauto_check ctable entry && check_aux tokens *)
      let okay = check_entry model tauto_check ctable entry in
      check_aux tokens && okay
  in
  check_aux tokens
