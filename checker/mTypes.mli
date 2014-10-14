(* Types for models. *)
type ident = string

type ivar = int
type bvar = int

type vprop =
| ILe of ivar*int
| IEq of ivar*int
| BTrue of bvar
| CTrue (* Constant true. *)

type lit =
| Pos of vprop
| Neg of vprop

type bound = (ivar * int) * int
type bounds = bound list

val negate : lit -> lit

type clause = lit list
