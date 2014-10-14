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
  | [< 'GL.Kwd "<=" ; 'GL.Int k >] -> MT.Pos (MT.ILe (ivar, k))
  | [< 'GL.Kwd "=" ; 'GL.Int k >] -> MT.Pos (MT.IEq (ivar, k))
  | [< 'GL.Kwd ">=" ; 'GL.Int k >] -> MT.Neg (MT.ILe (ivar, k-1))
  | [< 'GL.Kwd "!=" ; 'GL.Int k >] -> MT.Neg (MT.IEq (ivar, k))
  in parser
  | [< 'GL.Ident x ; prop = aux (M.get_ivar model x) >] -> prop
  | [< 'GL.Int k1 ; 'GL.Kwd "=" ; 'GL.Int k2 >] ->
      if k1 = k2 then MT.Pos MT.CTrue else MT.Neg MT.CTrue

let parse_lit model = parser
  | [< 'GL.Kwd "~" ; 'GL.Ident id >] ->
      MT.negate (M.get_lit model id)
  | [< 'GL.Ident id >] ->
      (M.get_lit model id)

let parse_clause model = S.listof (parse_lit model)
