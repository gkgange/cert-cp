(* Built-in checkers.
 * Additional checkers can also be registered
 * at runtime. *)
module R = Registry
module C = Checker
module MT = MTypes
module P = Parse
module S = Spec
module M = Model
module C_impl = Checker_impl

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
let ivar_list model = S.listof (P.parse_ivar model)

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
let linear_args model = S.cons int_list (S.cons (ivar_list model) S.intconst)

let check_linear_le model =
 fun tokens ->
   let (coeffs, (vars, k)) = linear_args model tokens in
(*     (S.cons int_list (S.cons (ivar_list model) S.intconst)) tokens in *)
   let linterms = List.map2 (fun c v -> (c, v)) coeffs vars in
   let repr = Format.sprintf "linear_le(%s, %s, %d)"
     (string_of_ints coeffs) (string_of_ivars model vars) k in
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

(* Build a _reified_ linear checker. *)
let check_reif_linear_le model =
  fun tokens ->
    let (r, (coeffs, (vars, k))) =
      (S.cons (P.parse_lit model) (linear_args model)) tokens in
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
          (C_impl.Elem (x, i, ys))
          (impl_clause_of_clause cl))
  }

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

let parse_cumul_args model = parser
  | [< xs = (ivar_list model) ; 'Genlex.Kwd "," ; durations = int_list ;
        'Genlex.Kwd "," ; resources = int_list ;
        'Genlex.Kwd "," ; lim = S.intconst >] ->
          (xs, durations, resources, lim)

let check_cumul model =
  fun tokens ->
    let (xs, durations, resources, lim) = parse_cumul_args model tokens in
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
let register () =
  R.add "linear_le" check_linear_le ;
  R.add "linear_le_reif" check_reif_linear_le ;
  R.add "element" check_element ;
  R.add "cumulative" check_cumul ;
  R.add "clause" check_clause
(*
  R.add "clause" R.null_checker ;
  R.add "linear_le" R.null_checker
  *)
