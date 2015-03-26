(* Model specification. *)
module MT = MTypes
module H = Hashtbl
module A = DynArray
module C = Checker
module Sol = SolCheck

type ident = MT.ident

let error str = failwith str

(* Symbol kind. *)
type ident_kind =
| IdBool (* Bool variable *)
| IdInt  (* Int variable *)
| IdCon  (* Constraint (with associated checker) *)
| IdProp (* Proposition *)

type constraint_info = {
  name : ident ;
  mutable checkers : C.t list ;
  mutable sol_check : Sol.t option ;
}
type model = {
  (* Symbol table. *)
  symbols : (ident, ident_kind*int) Hashtbl.t;

  bvars : ident A.t ;
  ivars : (ident * ((int*int) option)) A.t ;
  (* constraints : (ident * C.t) A.t; *)
  constraints : constraint_info A.t;
  vprops : (ident * MT.lit) A.t
}

type t = model

let create () = {
  symbols = Hashtbl.create 17 ;

  bvars = A.create ();
  ivars = A.create ();
  constraints = A.create ();
  vprops = A.create ();
}

(* Fixme: Add checking of duplicates. *)
let add_ivar model ident bounds =
  let idx = A.length model.ivars in
  Hashtbl.add model.symbols ident (IdInt, idx) ;
  A.add model.ivars (ident, bounds)

let add_bvar model ident =
  let idx = A.length model.bvars in
  Hashtbl.add model.symbols ident (IdBool, idx) ;
  A.add model.bvars ident

let add_lit model ident prop =
  let idx = A.length model.vprops in
  Hashtbl.add model.symbols ident (IdProp, idx) ;
  A.add model.vprops (ident, prop)

let constraint_id model ident =
  try
    let (kind, idx) = Hashtbl.find model.symbols ident in
    match kind with
    | IdCon -> idx
    | _ -> error (Format.sprintf "Error:  Identifier %s not a constraint." ident)
  with Not_found ->
    let idx = A.length model.constraints
    and elt = {
      name = ident ;
      checkers = [] ;
      sol_check = None
    } in
    begin
      Hashtbl.add model.symbols ident (IdCon, idx) ;
      A.add model.constraints elt ;
      idx
    end
    
let get_constraint_info model ident =
  A.get model.constraints (constraint_id model ident)

let add_checker model ident checker =
  let elt = get_constraint_info model ident in
  elt.checkers <- checker :: elt.checkers

let add_sol_check model ident sol_check =
  let elt = get_constraint_info model ident in
  elt.sol_check <- Some sol_check

let get_ivar (model : t) ident =
  try
    let (kind, idx) = Hashtbl.find model.symbols ident in
    match kind with
    | IdInt -> idx
    | _ -> error (Format.sprintf "Error: symbol %s not an integer variable." ident)
  with Not_found ->
    error (Format.sprintf "Error: symbol not found - %s." ident)

let ivar_name model ivar = fst (A.get model.ivars ivar)
let bvar_name model bvar = A.get model.bvars bvar

let get_bvar (model : t) ident =
  try
    let (kind, idx) = Hashtbl.find model.symbols ident in
    match kind with
    | IdBool -> idx
    | _ -> error (Format.sprintf "Error: symbol %s not an Boolean variable." ident)
  with Not_found ->
    error (Format.sprintf "Error: symbol not found - %s." ident)

let get_lit (model : t) ident =
  try
    let (kind, idx) = Hashtbl.find model.symbols ident in
    match kind with
    | IdProp -> snd (A.get model.vprops idx)
    | IdBool -> MT.Pos (MT.BTrue idx)
    | _ -> failwith (Format.sprintf "Error: symbol %s not a proposition." ident)
  with Not_found ->
    failwith (Format.sprintf "Error: symbol not found - %s." ident)

let lits_iteri f model = A.iteri (fun i (id, lit) -> f i id lit) model.vprops

let get_checker model ident =
  match (get_constraint_info model ident).checkers with
  | [] -> error (Format.sprintf "Error: No checker registered for %s." ident)
  | (x :: xs) -> x
  (*
  try
    let (kind, idx) = Hashtbl.find model.symbols ident in
    match kind with
    | IdCon -> snd (A.get model.constraints idx)
    | _ -> failwith (Format.sprintf "Error: symbol %s not a constraint." ident)
  with Not_found ->
    failwith (Format.sprintf "Error: symbol not found - %s." ident)
  *)

let get_all_checkers model =
  A.fold_left (fun cs elt -> List.append elt.checkers cs) [] model.constraints

let get_sol_checkers model =
  A.fold_left (fun cs elt ->
    match elt.sol_check with
    | Some check -> check :: cs
    | None -> (Sol.fail elt.name) :: cs) [] model.constraints

let string_of_vprop model = function
| MT.ILe (x, k) -> (ivar_name model x) ^ "<=" ^ (string_of_int k)
| MT.IEq (x, k) -> (ivar_name model x) ^ "=" ^ (string_of_int k)
| MT.BTrue x -> bvar_name model x
| MT.CTrue -> "T"

let string_of_lit model = function
| MT.Pos vp -> string_of_vprop model vp
| MT.Neg vp -> "~" ^ string_of_vprop model vp

let string_of_clause model cl =
  let rec aux = function
  | [] -> ""
  | [x] -> string_of_lit model x
  | (x :: xs) -> (string_of_lit model x) ^ ", " ^ (aux xs)
  in
  "[" ^ (aux cl) ^ "]"

let get_bounds model =
  let bnd = ref [] in
  begin
    A.iteri (fun i (_, xb) ->
     match xb with
     | None -> ()
     | Some (lb, ub) -> bnd := ((i, lb), ub) :: !bnd) model.ivars;
    !bnd
  end
