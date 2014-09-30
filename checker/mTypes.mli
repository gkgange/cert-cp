(* Types for models. *)
type ident = string

type ivar = int
type bvar = int

type vprop =
| ILe of ivar*int
| IEq of ivar*int
| BTrue of bvar

type lit =
| Pos of vprop
| Neg of vprop

type clause = lit list
