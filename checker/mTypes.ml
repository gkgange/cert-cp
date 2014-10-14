(* Types for models. *)
type ident = string

type ivar = int
type bvar = int

type vprop =
| ILe of ivar*int
| IEq of ivar*int
| BTrue of bvar
| CTrue

type lit =
| Pos of vprop
| Neg of vprop

type bound = (ivar * int) * int
type bounds = bound list

let negate = function
  | Pos vp -> Neg vp
  | Neg vp -> Pos vp

type clause = lit list
