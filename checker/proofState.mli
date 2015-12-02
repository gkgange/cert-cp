(* Header for model-level Coq interface *)
type ident = string

type model_info = {
  ivars : (ident, int) Hashtbl.t ;
  bounds : (int * int) option DynArray.t ;
  cst_idxs : (ident, int) Hashtbl.t ;
  csts : Checker_impl.cst DynArray.t
}

type literal_map = (int, Checker_impl.lit) Hashtbl.t

type proof_state
type t = proof_state

val parse_model_info : Genlex.token Stream.t -> model_info
val model_of_model_info : model_info -> Checker_impl.model

val add_cst_parser : ident -> (model_info -> Genlex.token Stream.t -> Checker_impl.cst) -> unit

val get_ivar : model_info -> ident -> int

val parse_lit_map : model_info -> Genlex.token Stream.t -> literal_map

val create : model_info -> literal_map -> Genlex.token Stream.t -> proof_state
val next : proof_state -> (Checker_impl.step * proof_state) option

val parse_step : model_info -> literal_map -> Genlex.token Stream.t -> Checker_impl.step
val parse_proof : model_info -> literal_map -> Genlex.token Stream.t -> Checker_impl.step list
