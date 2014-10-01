(* Parsing for different data-types. *)
(* val parse_vprop : model -> Genlex.token Stream.t -> vprop *)
module MT = MTypes
module M = Model
module GL = Genlex
module S = Spec

let parse_lit model = parser
  | [< 'GL.Kwd "~" ; 'GL.Ident id >] ->
      MT.Neg (M.get_vprop model id)
  | [< 'GL.Ident id >] ->
      MT.Pos (M.get_vprop model id)

let parse_clause model = S.listof (parse_lit model)
