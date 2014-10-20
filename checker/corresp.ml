(* Check correspondence between a model (with inferences)
 * and the initial clauses of a resolution proof. *)
module GL = Genlex
module MT = MTypes
module M = Model
module H = Hashtbl
module A = DynArray

let lmap_of_model model =
  let lmap = H.create 3037 in
  H.add lmap 254 (MT.Pos MT.CTrue) ;
  M.lits_iteri (fun i _ lit -> H.add lmap (255+i) lit) model ;
  lmap

let clause_table clauses =
  let ctable = H.create 11437 in
  H.add ctable [MT.Pos MT.CTrue] () ;
  List.iter (fun cl -> H.add ctable cl ()) clauses ;
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
  | [< 'GL.Int k >] -> (get_lit lmap k)


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

let check_clause model cltable clause =
  begin
    if !COption.verbosity > 1
    then
      let fmt = Format.std_formatter in
      Format.fprintf fmt "Checking %s@."
        (M.string_of_clause model clause)
  end ;
  try
    let _ = H.find cltable clause in
    true
  with Not_found ->
    if Builtins.tauto (M.get_bounds model) clause then
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

let check_entry model cltable (_, cl, ants) =
  match ants with
  | [] -> check_clause model cltable cl
  | _ -> true

let check model clauses tokens =
  let lmap = lmap_of_model model
  and ctable = clause_table clauses in
  let rec check_aux tokens =
    match Stream.peek tokens with
    | None ->
      (* Checked all entries in the resolution proof. *)
      true
    | _ ->
      (* Get the next entry. *)
      let entry = tentry lmap tokens in
      check_entry model ctable entry && check_aux tokens
  in
  check_aux tokens
