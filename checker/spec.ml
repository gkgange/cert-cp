(* Parameter specifications for constraints. *)
module S = Stream
open Genlex

type 'a spec = (token S.t -> 'a)

let keywords = ["(";")";";";",";":=";"|-";">=";"<=";"<";"=";"-";"~";"[";"]"]

(* )
let lexer stream = 
  let rec aux = parser
    | [< 'h; t=aux >] -> [< 'h; t >]
    | [< >] -> [< >] in
    (* drop_comments (aux (make_lexer keywords stream)) *)
    aux (make_lexer keywords stream)
( *)
let lexer stream =
  (*
  let rec aux t = parser
    | [< 'h; tl = aux (h :: t) >] -> tl
    | [< >] -> List.rev t
  in
  Stream.of_list (aux [] (make_lexer keywords stream))
  *)
  make_lexer keywords stream
(*  *)

let ident = parser
  | [< 'Ident s >] -> s
let intconst = parser
  | [< 'Kwd "-" ; 'Int n >] -> (-n)
  | [< 'Int n >] -> n
let boolconst = parser
  | [< 'Ident s >] -> bool_of_string s

let listof sub_parse =
  let rec tail = parser
    | [< 'Kwd "," ; k = sub_parse ; t = tail >] -> k :: t
    | [< >] -> [] in
  let aux = parser
    | [< k = sub_parse ; t = tail >] -> k :: t
    | [< >] -> []
  in parser
    | [< 'Kwd "[" ; elts = aux ; 'Kwd "]" >] -> elts

let cons p1 p2 = parser
  | [< e1 = p1 ; 'Kwd "," ; e2 = p2 >] -> (e1, e2)
