(* Stuff for parsing streaming-DRUP proofs. *)
type proof_line =
    Intro of int list
  | Infer of int list
  | Delete of int list
  | Hint of string option
  | Comment of string

type t = proof_line

val next : char Stream.t -> t option
