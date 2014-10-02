(* Model specification. *)
module MT = MTypes
module H = Hashtbl
module A = DynArray
module C = Checker

type ident = MT.ident

let error str = failwith str

(* Symbol kind. *)
type ident_kind =
| IdBool (* Bool variable *)
| IdInt  (* Int variable *)
| IdCon  (* Constraint (with associated checker) *)
| IdProp (* Proposition *)

type model = {
  (* Symbol table. *)
  symbols : (ident, ident_kind*int) Hashtbl.t;

  bvars : ident A.t ;
  ivars : (ident * ((int*int) option)) A.t ;
  constraints : (ident * C.t) A.t;
  vprops : (ident * MT.vprop) A.t
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

let add_vprop model ident prop =
  let idx = A.length model.vprops in
  Hashtbl.add model.symbols ident (IdProp, idx) ;
  A.add model.vprops (ident, prop)

let add_checker model ident checker =
  let idx = A.length model.constraints in
  Hashtbl.add model.symbols ident (IdCon, idx) ;
  A.add model.constraints (ident, checker)

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

let get_vprop (model : t) ident =
  try
    let (kind, idx) = Hashtbl.find model.symbols ident in
    match kind with
    | IdProp -> snd (A.get model.vprops idx)
    | IdBool -> MT.BTrue idx
    | _ -> failwith (Format.sprintf "Error: symbol %s not a proposition." ident)
  with Not_found ->
    failwith (Format.sprintf "Error: symbol not found - %s." ident)

let get_checker model ident =
  try
    let (kind, idx) = Hashtbl.find model.symbols ident in
    match kind with
    | IdCon -> snd (A.get model.constraints idx)
    | _ -> failwith (Format.sprintf "Error: symbol %s not a constraint." ident)
  with Not_found ->
    failwith (Format.sprintf "Error: symbol not found - %s." ident)

let string_of_vprop model = function
| MT.ILe (x, k) -> (ivar_name model x) ^ "<=" ^ (string_of_int k)
| MT.IEq (x, k) -> (ivar_name model x) ^ "=" ^ (string_of_int k)
| MT.BTrue x -> bvar_name model x

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
