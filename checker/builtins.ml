(* Registering parsers for coq csts *)
module St = Stream
module MT = MTypes
module P = Parse
module S = Spec
(* module M = Model *)
module Pr = ProofState
module C_impl = Checker_impl
module GL = Genlex

(* Parser helpers. *)
let int_list = S.listof S.intconst
let parse_ident = parser
  [< 'GL.Ident id >] -> id
let parse_ivar get_ivar toks = get_ivar (parse_ident toks)
let ivar_list get_ivar = S.listof (parse_ivar get_ivar)

let string_of_list f ls =
  let rec aux = function
    | [] -> ""
    | [x] -> f x
    | (x :: xs) -> (f x) ^ "," ^ (aux xs)
  in "[" ^ (aux ls) ^ "]"

let parse_iterm minfo toks =
  match St.next toks with
  | GL.Int k -> C_impl.Ilit k
  | GL.Ident x -> C_impl.Ivar (Pr.get_ivar minfo x)
  | _ -> failwith "Unexpected token in parse_iterm"

let string_of_ints = string_of_list string_of_int

(* Build the linear checker. *)
let linear_args get_ivar = S.cons int_list (S.cons (S.listof get_ivar) S.intconst)

let minfo_parse_linear_le minfo tokens =
   let (coeffs, (vars, k)) = linear_args (parse_iterm minfo) tokens in
   let linterms = List.map2 (fun c v -> (c, v)) coeffs vars in
   C_impl.make_linear linterms k

let minfo_parse_linear_ne minfo tokens =
   let (coeffs, (vars, k)) = linear_args (parse_iterm minfo) tokens in
   let linterms = List.map2 (fun c v -> (c, v)) coeffs vars in
   C_impl.make_lin_ne linterms k


(* FIXME: Add clause parser *)
let minfo_parse_vprop minfo = 
  let aux x = parser
    | [< 'GL.Kwd "<=" ; k = S.intconst >] -> C_impl.Pos (C_impl.ILeq (x, k))
    | [< 'GL.Kwd "<" ; k = S.intconst >] -> C_impl.Pos (C_impl.ILeq (x, (k-1)))
    | [< 'GL.Kwd "=" ; k = S.intconst >] -> C_impl.Pos (C_impl.IEq (x, k))
    | [< 'GL.Kwd ">" ; k = S.intconst >] -> C_impl.Neg (C_impl.ILeq (x, k))
    | [< 'GL.Kwd ">=" ; k = S.intconst >] -> C_impl.Neg (C_impl.ILeq (x, (k-1)))
  in
  parser
    | [< 'GL.Ident "true" >] -> C_impl.Pos C_impl.CTrue
    | [< 'GL.Ident "false" >] -> C_impl.Neg C_impl.CTrue
    | [< 'GL.Ident x ; vp = aux (Pr.get_ivar minfo x) >] -> vp

let neglit = function
  | C_impl.Pos vp -> C_impl.Neg vp
  | C_impl.Neg vp -> C_impl.Pos vp
            
let minfo_parse_lit minfo = parser
  | [< 'GL.Kwd "~" ; vp = minfo_parse_vprop minfo >] -> neglit vp
  | [< vp = minfo_parse_vprop minfo >] -> vp

let minfo_parse_clause minfo toks =
  let cl0 = S.listof (minfo_parse_lit minfo) toks in 
  C_impl.make_clause cl0

let parse_element minfo tokens =
  let (x, (i, ys)) =
    (S.cons
      (parse_iterm minfo)
      (S.cons (parse_iterm minfo) (S.listof (parse_iterm minfo)))) tokens in
  C_impl.make_element x i ys

let make_cumul xs durations resources lim =
  let rec tasks ys ds rs = match ys with
    | [] -> []
    | (y :: yt) ->
        { C_impl.duration = (List.hd ds) ;
          C_impl.resource = (List.hd rs) ;
          C_impl.svar = y
        } :: (tasks yt (List.tl ds) (List.tl rs))
  in {
    C_impl.tasks = tasks xs durations resources ;
    C_impl.limit = lim
  }

let parse_cumul_args get_iterm = parser
  | [< xs = (S.listof get_iterm) ; 'Genlex.Kwd "," ; durations = (S.listof get_iterm) ;
        'Genlex.Kwd "," ; resources = S.listof get_iterm ;
        'Genlex.Kwd "," ; lim = get_iterm >] ->
          (xs, durations, resources, lim)

let parse_cumul model tokens =
  let (xs, durations, resources, lim) = parse_cumul_args (parse_iterm model) tokens in
  C_impl.make_cumul (make_cumul xs durations resources lim)
;;

let chomp tok toks =
  match Stream.next toks with
  | t' when tok = t' -> ()
  | _ -> failwith "Token match failed."

let parse_conj model tokens =
  let x = Pr.parse_cst model tokens in
  chomp (GL.Kwd ",") tokens ;
  let y = Pr.parse_cst model tokens in
  C_impl.Conj (x, y)

let parse_disj model tokens =
  let x = Pr.parse_cst model tokens in
  chomp (GL.Kwd ",") tokens ;
  let y = Pr.parse_cst model tokens in
  C_impl.Disj (x, y)

let parse_half model tokens =
  let r = minfo_parse_lit model tokens in
  chomp (GL.Kwd ",") tokens ;
  let c = Pr.parse_cst model tokens in
  C_impl.Half (r, c)

let parse_memb model toks =
   let z = parse_iterm model toks in
   chomp (GL.Kwd ",") toks ;
   let xs = S.listof (parse_iterm model) toks in
   C_impl.make_memb z xs

let parse_notmemb model toks =
   let z = parse_iterm model toks in
   chomp (GL.Kwd ",") toks ;
   let xs = S.listof (parse_iterm model) toks in
   C_impl.make_notmemb z xs

let op_of_id id =
  match id with
  | "add" -> C_impl.Plus
  | "mul" -> C_impl.Times
  | "sub" -> C_impl.Sub
  | "div" -> C_impl.Div
  | "min" -> C_impl.Min
  | "max" -> C_impl.Max
  | _ -> failwith (Format.sprintf "Expected arithmetic operator, got %s" id)

let unop_of_id id =
  match id with
  | "neg" -> C_impl.Uminus
  | "abs" -> C_impl.Abs
  | _ -> failwith (Format.sprintf "Expected unary arithmetic operator, got %s" id)

let rec parse_arith model tokens =
  match St.next tokens with
  | GL.Ident id ->
    begin
    match St.peek tokens with
    | Some (GL.Kwd "(") ->
      let _ = St.junk tokens in
      let x = parse_arith model tokens in
      begin
        match St.peek tokens with
        | Some (GL.Kwd ",") ->
          St.junk tokens ;
          let y = parse_arith model tokens in
          chomp (GL.Kwd ")") tokens ;
          C_impl.Op (op_of_id id, x, y)
        | _ ->
          chomp (GL.Kwd ")") tokens ;
          C_impl.Un (unop_of_id id, x)
      end
    | _ -> C_impl.T (C_impl.Ivar (Pr.get_ivar model id))
    end
  | GL.Int k -> C_impl.T (C_impl.Ilit k)
  | _ -> failwith "Expected arithmetic expression"


let parse_arith_eq model tokens =
  let z = parse_iterm model tokens in
  chomp (GL.Kwd ",") tokens ;
  let exp = parse_arith model tokens in
  C_impl.make_arith_eq z exp

let parse_arith_ne model tokens =
  let z = parse_iterm model tokens in
  chomp (GL.Kwd ",") tokens ;
  let exp = parse_arith model tokens in
  C_impl.make_arith_ne z exp

let register () =
  Pr.add_cst_parser "linear_le" minfo_parse_linear_le ;
  Pr.add_cst_parser "linear_ne" minfo_parse_linear_ne ;
  Pr.add_cst_parser "element" parse_element ;
  Pr.add_cst_parser "cumulative" parse_cumul ;
  Pr.add_cst_parser "memb" parse_memb ;
  Pr.add_cst_parser "notmemb" parse_notmemb ;
  Pr.add_cst_parser "clause" minfo_parse_clause ;
  Pr.add_cst_parser "and" parse_conj ;
  Pr.add_cst_parser "or" parse_disj ;
  Pr.add_cst_parser "half" parse_half ;
  Pr.add_cst_parser "equal" parse_arith_eq ;
  Pr.add_cst_parser "neq" parse_arith_ne

