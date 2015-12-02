(* Built-in checkers.
 * Additional checkers can also be registered
 * at runtime. *)
module R = Registry
module C = Checker
module Sol = SolCheck
module MT = MTypes
module P = Parse
module S = Spec
module M = Model
module Pr = ProofState
module C_impl = Checker_impl
module GL = Genlex

(* Conversion between internal types, and Coq-extracted types. *)
let impl_vprop_of_vprop = function
| MT.ILe (x, k) -> C_impl.ILeq (x, k)
| MT.IEq (x, k) -> C_impl.IEq (x, k)
| MT.BTrue x -> C_impl.BTrue (x)
| MT.CTrue -> C_impl.CTrue

let impl_lit_of_lit = function
| MT.Pos vp -> C_impl.Pos (impl_vprop_of_vprop vp)
| MT.Neg vp -> C_impl.Neg (impl_vprop_of_vprop vp)

let impl_clause_of_clause = List.map impl_lit_of_lit 
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
let string_of_ivars model = string_of_list (M.ivar_name model)

(* Checker for a tautological clause. *)
let tauto bnd cl =
  C_impl.check_tauto_bnd bnd (impl_clause_of_clause cl)
let tauto_dbnd dbnd cl =
  C_impl.check_tauto_dbnd dbnd (impl_clause_of_clause cl)

let clause_subsumes cl_x cl_y =
  C_impl.check_clause (impl_clause_of_clause cl_x) (impl_clause_of_clause cl_y)

(* Build the linear checker. *)
let linear_args get_ivar = S.cons int_list (S.cons (ivar_list get_ivar) S.intconst)

let parse_linear_le model tokens =
   let (coeffs, (vars, k)) = linear_args (M.get_ivar model) tokens in
   let linterms = List.map2 (fun c v -> (c, v)) coeffs vars in
   let repr = Format.sprintf "linear_le(%s, %s, %d)"
     (string_of_ints coeffs) (string_of_ivars model vars) k in
   ((linterms, k), repr)

let minfo_parse_linear_le minfo tokens =
   let (coeffs, (vars, k)) = linear_args (Pr.get_ivar minfo) tokens in
   let linterms = List.map2 (fun c v -> (c, v)) coeffs vars in
   C_impl.make_linear linterms k

let check_linear_le model =
 fun tokens ->
   (*
   let (coeffs, (vars, k)) = linear_args model tokens in
   let linterms = List.map2 (fun c v -> (c, v)) coeffs vars in
   let repr = Format.sprintf "linear_le(%s, %s, %d)"
     (string_of_ints coeffs) (string_of_ivars model vars) k in
   *)
   let ((linterms, k), repr) = parse_linear_le model tokens in
   let bnd = M.get_bounds model in
   let dset = C_impl.bounds_domset bnd in
{
  C.repr = repr ;
  C.check =
    (*
    (fun bnd cl ->
      C_impl.check_lincon (linterms, k) (impl_clause_of_clause cl)
      || C_impl.check_linear_bnd (linterms, k) bnd (impl_clause_of_clause cl)
    )
*)
    (fun _ cl ->
      C_impl.check_linear_dbnd (linterms, k) dset (impl_clause_of_clause cl))
}

let check_linear_le_sol model =
 fun tokens ->
   let ((linterms, k), repr) = parse_linear_le model tokens in
   (* let bnd = M.get_bounds model in
   let dset = C_impl.bounds_domset bnd in *)
{
  Sol.repr = repr ;
  Sol.check =
    (*
    (fun bnd cl ->
      C_impl.check_lincon (linterms, k) (impl_clause_of_clause cl)
      || C_impl.check_linear_bnd (linterms, k) bnd (impl_clause_of_clause cl)
    )
*)
    (fun asg ->
      let asg_map = C_impl.asg_of_alist asg in
      C_impl.check_lincon_sol (linterms, k) asg_map)
}

(* Build a _reified_ linear checker. *)
let check_reif_linear_le model =
  fun tokens ->
    let (r, (coeffs, (vars, k))) =
      (S.cons (P.parse_lit model) (linear_args (M.get_ivar model))) tokens in
    let linterms = List.map2 (fun c v -> (c, v)) coeffs vars in
    let repr = Format.sprintf "linear_le_reif(%s, %s, %s, %d)"
      (M.string_of_lit model r)
      (string_of_ints coeffs)
      (string_of_ivars model vars) k in
    let bnd = M.get_bounds model in
    let dset = C_impl.bounds_domset bnd in
    {
      C.repr = repr ;
      C.check = (fun _ cl ->
        C_impl.check_reif_linear_dbnd
          (impl_lit_of_lit r)
          (linterms, k) dset
          (impl_clause_of_clause cl))
    }

(* FIXME: Add clause parser *)
(*
let minfo_parse_clause minfo toks =
  let cl0 = 
*)

let check_clause model =
  fun tokens ->
    let cl0 = P.parse_clause model tokens in
    let repr = Format.sprintf "clause(%s)"
      (M.string_of_clause model cl0) in
    {
      C.repr = repr;
      C.check = (fun _ cl ->
         C_impl.check_clause
           (impl_clause_of_clause cl0)
           (impl_clause_of_clause cl))
    }

let check_element model =
  fun tokens ->
    let (x, (i, ys)) =
      (S.cons
        (P.parse_ivar model)
        (S.cons (P.parse_ivar model) int_list)) tokens in
    let repr = Format.sprintf "element(%s, %s, %s)"
      (M.ivar_name model x) (M.ivar_name model i) (string_of_ints ys) in
  {
    C.repr = repr ;
    C.check =
      (fun _ cl ->
        C_impl.check_element
          (C_impl.Element (x, i, ys))
          (impl_clause_of_clause cl))
  }

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

let check_cumul model =
  fun tokens ->
    let (xs, durations, resources, lim) = parse_cumul_args (M.get_ivar model) tokens in
    let cumul = make_cumul xs durations resources lim in
    let repr = Format.sprintf "cumulative(%s, %s, %s, %d)"
      (string_of_ivars model xs) (string_of_ints durations)
      (string_of_ints resources) lim in
    let bnd = M.get_bounds model in
    let dset = C_impl.bounds_domset bnd in
    {
      C.repr = repr ;
      C.check = (fun _ cl ->
        let icl = impl_clause_of_clause cl in
        (* C_impl.check_cumul_bnd cumul bnd icl *)
        (* C_impl.check_cumul_tt_bnd cumul bnd icl *)
        C_impl.check_cumul_tt_dbnd cumul dset icl
      )
    }

let parse_cumul model tokens =
  let (xs, durations, resources, lim) = parse_cumul_args (Pr.get_ivar model) tokens in
  C_impl.make_cumul (make_cumul xs durations resources lim)
;;

let check_cumul_sol model =
  fun tokens ->
    let (xs, durations, resources, lim) = parse_cumul_args (M.get_ivar model) tokens in
    let cumul = make_cumul xs durations resources lim in
    let repr = Format.sprintf "cumulative(%s, %s, %s, %d)"
      (string_of_ivars model xs) (string_of_ints durations)
      (string_of_ints resources) lim in
    {
      Sol.repr = repr ;
      Sol.check = (fun asg ->
        let asg_map = C_impl.asg_of_alist asg in
        C_impl.check_cumul_sol cumul asg_map
      )
    }

let register () =
  R.add "linear_le" check_linear_le ;
  R.add "linear_le_reif" check_reif_linear_le ;
  R.add "element" check_element ;
  R.add "cumulative" check_cumul ;
  R.add "clause" check_clause ;

  Pr.add_cst_parser "linear_le" minfo_parse_linear_le ;
(*  Pr.add_cst_parser "linear_le_reif" parse_reif_linear_le ; *)
  Pr.add_cst_parser "element" parse_element ;
  Pr.add_cst_parser "cumulative" parse_cumul ;
  (* Pr.add_cst_parser "clause" parse_clause ; *)

  R.add_sol "linear_le" check_linear_le_sol ;
  R.add_sol "cumulative" check_cumul_sol

