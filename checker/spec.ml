(* Parameter specifications for constraints. *)
module S = Stream
open Genlex

type 'a spec = (token S.t -> 'a)

let keywords = ["(";")";";";",";":=";"|-";"<=";"<";"~";"[";"]"]

let lexer stream = 
  let rec aux = parser
    | [< 'h; t=aux >] -> [< 'h; t >]
    | [< >] -> [< >] in
    aux (make_lexer keywords stream)

let ident = parser
  | [< 'Ident s >] -> s
let intconst = parser
  | [< 'Int n >] -> n
let boolconst = parser
  | [< 'Ident s >] -> bool_of_string s

let listof sub_parse =
  let rec aux = parser
    | [< k = sub_parse ; 'Kwd "," ; t = aux >] -> k :: t
    | [< k = sub_parse >] -> [k]
    | [< >] -> []
  in parser
    | [< 'Kwd "[" ; elts = aux ; 'Kwd "]" >] -> elts

let cons p1 p2 = parser
  | [< e1 = p1 ; e2 = p2 >] -> (e1, e2)
