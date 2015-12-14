(* Registering parsers for coq csts *)
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

let string_of_ints = string_of_list string_of_int

(* Build the linear checker. *)
let linear_args get_ivar = S.cons int_list (S.cons (ivar_list get_ivar) S.intconst)

let minfo_parse_linear_le minfo tokens =
   let (coeffs, (vars, k)) = linear_args (Pr.get_ivar minfo) tokens in
   let linterms = List.map2 (fun c v -> (c, v)) coeffs vars in
   C_impl.make_linear linterms k


(* FIXME: Add clause parser *)
(*
let minfo_parse_clause minfo toks =
  let cl0 = 
    *)

let parse_element minfo tokens =
  let (x, (i, ys)) =
    (S.cons
      (parse_ivar (Pr.get_ivar minfo))
      (S.cons (parse_ivar (Pr.get_ivar minfo)) int_list)) tokens in
  C_impl.make_element x i ys

let make_cumul xs durations resources lim =
  let rec tasks ys ds rs = match ys with
    | [] -> []
    | (y :: yt) ->
        { C_impl.duration = C_impl.nat_of_int (List.hd ds) ;
          C_impl.resource = C_impl.nat_of_int (List.hd rs) ;
          C_impl.svar = y
        } :: (tasks yt (List.tl ds) (List.tl rs))
  in {
    C_impl.tasks = tasks xs durations resources ;
    C_impl.limit = C_impl.nat_of_int lim
  }

let parse_cumul_args get_ivar = parser
  | [< xs = (ivar_list get_ivar) ; 'Genlex.Kwd "," ; durations = int_list ;
        'Genlex.Kwd "," ; resources = int_list ;
        'Genlex.Kwd "," ; lim = S.intconst >] ->
          (xs, durations, resources, lim)

let parse_cumul model tokens =
  let (xs, durations, resources, lim) = parse_cumul_args (Pr.get_ivar model) tokens in
  C_impl.make_cumul (make_cumul xs durations resources lim)
;;

let register () =
  Pr.add_cst_parser "linear_le" minfo_parse_linear_le ;
  Pr.add_cst_parser "element" parse_element ;
  Pr.add_cst_parser "cumulative" parse_cumul ;
