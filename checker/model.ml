(* Model specification. *)
module MT = MTypes
module H = Hashtbl
module A = DynArray
module C = Checker

type ident = MT.ident

(* Symbol kind. *)
type ident_kind =
| IdBool (* Bool variable *)
| IdInt  (* Int variable *)
| IdCon  (* Constraint (with associated checker) *)
| IdProp (* Proposition *)

type model = {
  (* Symbol table. *)
  symbols : (ident, ident_kind*int) Hashtbl.t;

  bvar_names : ident A.t ;
  ivar_names : ident A.t ;
  constraints : (ident * C.t) A.t;
  vprops : (ident * MT.vprop) A.t
}

type t = model

let create () = {
  symbols = Hashtbl.create 17 ;

  bvar_names = A.create ();
  ivar_names = A.create ();
  constraints = A.create ();
  vprops = A.create ();
}

(* Fixme: Add checking of duplicates. *)
let add_ivar model ident =
  let idx = A.length model.ivar_names in
  Hashtbl.add model.symbols ident (IdInt, idx) ;
  A.add model.ivar_names ident

let add_bvar model ident =
  let idx = A.length model.bvar_names in
  Hashtbl.add model.symbols ident (IdBool, idx) ;
  A.add model.bvar_names ident

let add_vprop model ident prop =
  let idx = A.length model.vprops in
  Hashtbl.add model.symbols ident (IdProp, idx) ;
  A.add model.vprops (ident, prop)

let add_checker model ident checker =
  let idx = A.length model.constraints in
  Hashtbl.add model.symbols ident (IdCon, idx) ;
  A.add model.constraints (ident, checker)

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
