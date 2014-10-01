(* Parsing for different data-types. *)
(* val parse_vprop : model -> Genlex.token Stream.t -> vprop *)
module MT = MTypes
module M = Model
module GL = Genlex
module S = Spec

let parse_ivar model tokens = M.get_ivar model (S.ident tokens)
let parse_bvar model tokens = M.get_bvar model (S.ident tokens)
let parse_vprop model =
  let aux ivar = parser
  | [< 'GL.Kwd "<=" ; 'GL.Int k >] -> MT.ILe (ivar, k)
  | [< 'GL.Kwd "=" ; 'GL.Int k >] -> MT.IEq (ivar, k)
  in parser
  | [< 'GL.Ident x ; prop = aux (M.get_ivar model x) >] -> prop

let parse_lit model = parser
  | [< 'GL.Kwd "~" ; 'GL.Ident id >] ->
      MT.Neg (M.get_vprop model id)
  | [< 'GL.Ident id >] ->
      MT.Pos (M.get_vprop model id)

let parse_clause model = S.listof (parse_lit model)
