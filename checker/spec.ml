(* Parameter specifications for constraints. *)
module S = Stream
open Genlex

type 'a spec = (token S.t -> 'a)

let keywords = ["(";")";";";",";":=";"|-";">=";"<=";"<";"=";"-";"~";"[";"]"]

let lexer stream =
  make_lexer keywords stream

let ident = parser
  | [< 'Ident s >] -> s
let intconst = parser
  | [< 'Kwd "-" ; 'Int n >] -> (-n)
  | [< 'Int n >] -> n
let boolconst = parser
  | [< 'Ident s >] -> bool_of_string s

(*
let listof sub_parse =
  let rec tail = parser
    | [< 'Kwd "," ; k = sub_parse ; t = tail >] -> k :: t
    | [< >] -> [] in
  let aux = parser
    | [< k = sub_parse ; t = tail >] -> k :: t
    | [< >] -> []
  in parser
    | [< 'Kwd "[" ; elts = aux ; 'Kwd "]" >] -> elts
    *)
let listof sub_parse =
  let rec tail es = parser
    | [< 'Kwd "," ; k = sub_parse ; xs = tail (k :: es) >] -> xs
    | [< >] -> List.rev es in
  let aux = parser
    | [< k = sub_parse ; xs = tail [k] >] -> xs
    | [< >] -> []
  in parser
    | [< 'Kwd "[" ; elts = aux ; 'Kwd "]" >] -> elts

let cons p1 p2 = parser
  | [< e1 = p1 ; 'Kwd "," ; e2 = p2 >] -> (e1, e2)
