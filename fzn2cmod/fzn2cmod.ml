module S = Stream
module H = Hashtbl
module Dy = DynArray
module U = Util

open Token
module P = Parser

module Pr = Problem

exception Unknown_constraint of string

type arith =
  | Int of int
  | Var of string
  | Plus of arith * arith
  | Times of arith * arith
  | Sub of arith * arith
  | Div of arith * arith
  | Min of arith * arith
  | Max of arith * arith

let get_arith = function
  | Pr.Ilit k -> Int k
  | Pr.Ivar v -> Var v
  | Pr.Blit b -> Int (if b then 1 else 0)
  | Pr.Bvar v -> Var v
  | _ -> failwith "Type mismatch in get_arith"

let rec print_arith fmt = function
  | Int k -> Format.pp_print_int fmt k
  | Var v -> Format.pp_print_string fmt v
  | Plus (x, y) -> print_ariths "add" [|x; y|] fmt
  | Times (x, y) -> print_ariths "mul" [|x; y|] fmt
  | Sub (x, y) -> print_ariths "sub" [|x; y|] fmt
  | Div (x, y) -> print_ariths "div" [|x; y|] fmt
  | Min (x, y) -> print_ariths "min" [|x; y|] fmt
  | Max (x, y) -> print_ariths "max" [|x; y|] fmt
and print_ariths ident args fmt =
  Format.fprintf fmt "%s@[<hov 1>(" ident ;
  Util.print_array ~pre:"" ~post:")@]" ~sep:",@," print_arith fmt args

(* Argument manipulation stuff *)
let rec resolve_arg problem arg =
  match arg with
  | Pr.Ilit k -> Pr.Ilit k
  | Pr.Ivar v -> Pr.Ivar (Pr.ival_name problem v)
  | Pr.Blit b -> Pr.Blit b
  | Pr.Bvar v -> Pr.Bvar (Pr.bval_name problem v)
  | Pr.Set s -> Pr.Set s
  | Pr.Arr xs -> Pr.Arr (Array.map (resolve_arg problem) xs)

let put = Format.fprintf

let cons_printers = H.create 17

let cons_idx = ref 0


let default_printer fmt problem args = 
  Format.pp_print_string fmt "true"
  (* Format.fprintf fmt "c%d := true" !cons_idx *)

let rec print_arg fmt arg =
  match arg with
  | Pr.Ilit k -> Format.pp_print_int fmt k
  | Pr.Ivar v -> Format.pp_print_string fmt v
  | Pr.Bvar v -> Format.fprintf fmt "%s >= 1" v
  | Pr.Blit b -> Format.pp_print_string fmt (string_of_bool b)
  | Pr.Set s -> failwith "Sets not currently supported by certcp."
  | Pr.Arr xs -> Util.print_array print_arg ~pre:"@[<hov 1>[" ~post:"@]]" ~sep:",@," fmt xs

let print_call fmt ident args =
  Format.fprintf fmt "%s(" ident ;
  Util.print_array print_arg ~pre:"@[<hov 1>" ~post:"@]" ~sep:",@," fmt args ;
  Format.fprintf fmt ")"

(* linear_le([1, -1], [v0, v8], -2), *)
(*
let print_linear suff fmt pr args =
(*
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array Pr.get_ivar args.(1) in
  let k = Pr.get_int args.(2) in
  *)
  Format.fprintf fmt "linear_%s(" suff ;
  (*
  Util.print_array Format.pp_print_int fmt ~pre:"@[<hov 1>[" ~post:"@]],@," ~sep:",@," cs ;
  Util.print_array Format.pp_print_string fmt ~pre:"@[<hov 1>[" ~post:"@]]" ~sep:",@," xs ;
  *)
  print_args fmt args ;
  (* Format.fprintf fmt ",@,%d)" k *)
  Format.fprintf fmt ")"
  *)

let print_linear suff args fmt = print_call fmt ("linear_" ^ suff) args
let print_linear_ge args fmt = 
  let coeffs = Array.map (fun x -> Pr.Ilit (-x)) (Pr.get_array Pr.get_int args.(0)) in
  let args' = [| Pr.Arr coeffs ; args.(1); Pr.Ilit (- (Pr.get_int args.(2))) |] in
  print_linear "le" args' fmt

let print_element args fmt = print_call fmt "element" [|args.(2); args.(0); args.(1)|]
let print_cumulative args fmt = print_call fmt "cumulative" args
let print_alldiff args fmt = print_call fmt "all_different" args

let print_pos fmt = function
  | Pr.Bv_bool b -> Format.pp_print_string fmt (string_of_bool b)
  | Pr.Bv_var v -> Format.fprintf fmt "%s >= 1" v

let print_neg fmt = function
  | Pr.Bv_bool b -> Format.pp_print_string fmt (string_of_bool (not b))
  | Pr.Bv_var v -> Format.fprintf fmt "%s < 1" v

type atom = Pos of string Pr.bval | Neg of string Pr.bval

let get_atom e = Pos (Pr.get_bval e)

let negate = function
  | Pos b -> Neg b
  | Neg b -> Pos b

let print_atom fmt = function
  | Pos b -> print_pos fmt b
  | Neg b -> print_neg fmt b

let print_clause args fmt =
  let pos = Pr.get_array (fun arg -> Pos (Pr.get_bval arg)) args.(0) in
  let neg = Pr.get_array (fun arg -> Neg (Pr.get_bval arg)) args.(1) in
  Util.print_array
    ~sep:",@," ~pre:"clause(@[<hov 1>[" ~post:"@]])" print_atom fmt (Array.append pos neg) 

let print_seq id (p_funs : (Format.formatter -> unit) list) fmt =
  Format.fprintf fmt "%s" id ;
  Util.print_list ~pre:"@[<hov 1>(" ~post:")@]" ~sep:",@,"
    (fun fmt p_fun -> p_fun fmt) fmt p_funs

let print_conj cons = print_seq "and" cons

let print_linear_eq args = print_conj [ print_linear "le" args ; print_linear_ge args ]
  
let print_half r (p_cons : (Format.formatter -> unit)) = print_seq "half" [(fun fmt -> print_atom fmt r); p_cons]

let print_equal x y = print_ariths "equal" [|x; y|]
let print_neq x y = print_ariths "neq" [|x; y|]
let print_eq_reif r x y = print_seq "and" [print_half r (print_ariths "equal" [|x; y|]) ; print_half (negate r) (print_ariths "neq" [|x; y|]) ]
let print_neq_reif r x y = print_seq "and" [print_half r (print_ariths "neq" [|x; y|]) ; print_half (negate r) (print_ariths "equal" [|x; y|]) ]

let init_printers () =
  let handlers =
    [ "int_lin_le", (fun fmt pr args -> print_linear "le" args fmt) ;
      "int_lin_eq", (fun fmt pr args -> print_linear_eq args fmt) ;
      "int_lin_ne", (fun fmt pr args -> print_linear "ne" args fmt) ;
      "int_lin_le_reif",
        (fun fmt pr args ->
          let r = get_atom args.(3) in
          print_conj
            [print_half r (print_linear "le" [|args.(0); args.(1); args.(2)|]) ;
            (print_half (negate r) (print_linear_ge [|args.(0); args.(1); Pr.Ilit ((Pr.get_int args.(2)) + 1)|]))] fmt) ;
      "int_lin_eq_reif",
        (fun fmt pr args ->
          let r = get_atom args.(3) in
          print_conj
            [print_half r (print_linear_eq [|args.(0); args.(1); args.(2)|]) ;
            (print_half (negate r) (print_linear "ne" [|args.(0); args.(1); args.(2)|]))] fmt) ;
      "int_lin_ne_reif",
        (fun fmt pr args ->
          let r = get_atom args.(3) in
          print_conj
            [print_half r (print_linear "ne" [|args.(0); args.(1); args.(2)|]) ;
            (print_half (negate r) (print_linear_eq [|args.(0); args.(1); args.(2)|]))] fmt) ;
      "array_int_element", (fun fmt pr args -> print_element args fmt) ;
      "array_var_int_element", (fun fmt pr args -> print_element args fmt) ;
      "chuffed_cumulative", (fun fmt pr args -> print_cumulative args fmt) ;
      (* "all_different_int", print_alldiff ; *)
      (* We replace bool2int with x = y. *)
      "int_eq", (fun fmt pr args -> print_equal (get_arith args.(0)) (get_arith args.(1)) fmt) ;
      "int_ne", (fun fmt pr args -> print_neq (get_arith args.(0)) (get_arith args.(1)) fmt) ;
      "int_le", (fun fmt pr args -> print_linear "le" [| Pr.Arr [|Pr.Ilit 1; Pr.Ilit (-1)|] ; Pr.Arr [|args.(0) ; args.(1)|]; Pr.Ilit 0 |] fmt) ;
      "int_lt", (fun fmt pr args -> print_linear "le" [| Pr.Arr [|Pr.Ilit 1; Pr.Ilit (-1)|] ; Pr.Arr [|args.(0) ; args.(1)|]; Pr.Ilit (-1) |] fmt) ;
      "int_le_reif",
        (fun fmt pr args ->
          let r = get_atom args.(2) in
          print_conj
            [print_half r @@ print_linear "le" [| Pr.Arr [|Pr.Ilit 1; Pr.Ilit (-1)|] ; Pr.Arr [|args.(0) ; args.(1)|]; Pr.Ilit 0 |] ;
             print_half (negate r) @@ print_linear "le" [| Pr.Arr [|Pr.Ilit (-1); Pr.Ilit 1|] ; Pr.Arr [|args.(0) ; args.(1)|]; Pr.Ilit (-1) |]] fmt) ;
      "int_lt_reif",
        (fun fmt pr args ->
          let r = get_atom args.(2) in
          print_conj
            [print_half r (print_linear "le" [| Pr.Arr [|Pr.Ilit 1; Pr.Ilit (-1)|] ; Pr.Arr [|args.(0) ; args.(1)|]; Pr.Ilit (-1) |]) ;
             print_half (negate r) (print_linear "le" [| Pr.Arr [|Pr.Ilit (-1); Pr.Ilit 1|] ; Pr.Arr [|args.(0) ; args.(1)|]; Pr.Ilit 0 |])] fmt) ;
      "int_max", (fun fmt pr args ->
        print_equal
          (get_arith args.(2))
          (Max (get_arith args.(0), get_arith args.(1))) fmt) ;
      "int_min", (fun fmt pr args ->
        print_equal 
          (get_arith args.(2))
          (Min (get_arith args.(0), get_arith args.(1))) fmt) ;
      "int_times", (fun fmt pr args ->
        print_equal
          (get_arith args.(2))
          (Times (get_arith args.(0), get_arith args.(1))) fmt) ;
      "int_div", (fun fmt pr args ->
        print_equal
          (get_arith args.(2))
          (Div (get_arith args.(0), get_arith args.(1))) fmt) ;
      "int_eq_reif", (fun fmt pr args ->
        let r = get_atom args.(2) in
        print_conj
          [print_half r (print_equal (get_arith args.(0)) (get_arith args.(1))) ;
           print_half (negate r) (print_neq (get_arith args.(0)) (get_arith args.(1)))] fmt) ;
      "int_ne_reif", (fun fmt pr args ->
        let r = get_atom args.(2) in
        print_conj
          [print_half r (print_neq (get_arith args.(0)) (get_arith args.(1)));
           print_half (negate r) (print_equal (get_arith args.(0)) (get_arith args.(1)))] fmt) ;
      "bool2int" ,
        (fun fmt pr args -> print_equal (get_arith args.(0)) (get_arith args.(1)) fmt) ;
      "bool_clause", (fun fmt pr args -> print_clause args fmt) ;
      "bool_eq_reif", (fun fmt pr args ->
        let r = get_atom args.(2) in
        print_conj
          [print_half r (print_equal (get_arith args.(0)) (get_arith args.(1))) ;
           print_half (negate r) (print_neq (get_arith args.(0)) (get_arith args.(1)))] fmt) ;
      "bool_xor", (fun fmt pr args ->
        let r = get_atom args.(2) in
        print_conj
          [print_half r (print_neq (get_arith args.(0)) (get_arith args.(1))) ;
           print_half (negate r) (print_equal (get_arith args.(0)) (get_arith args.(1)))] fmt) ;
      (* "bool_sum_le", (fun fmt pr args -> print_linear "le" args fmt) ; *)
      ]
  in
  List.iter (fun (id, hnd) -> H.add cons_printers id hnd) handlers

let print_constraint fmt problem cons_id cons_args =
  incr cons_idx ;
  Format.fprintf fmt "c%d := @[<v 3>" !cons_idx ;
  (* Do something about the arguments *)
  let res_args = Array.map (resolve_arg problem) cons_args in
  begin
    try
      let printer = H.find cons_printers cons_id in
      printer fmt problem res_args
    with Not_found ->
      begin
        Format.fprintf Format.err_formatter "WARNING: No printer for %s@." cons_id ;
        H.add cons_printers cons_id default_printer ;
        default_printer fmt problem res_args
      end
  end ;
  Format.fprintf fmt "@]"
  
(* type ival_info = { id : ident ; dom : Dom.t ; ann : ann_expr list } *)
let print_ivars fmt problem =
  Dy.iter (fun info ->
    Format.fprintf fmt ",@ " ;
    match info.Pr.dom with
    | Dom.Range (l, u) -> Format.fprintf fmt "%s := int %d %d" info.Pr.id l u
    | Dom.Set [k] -> Format.fprintf fmt "%s := int %d %d" info.Pr.id k k
    | Dom.Set [a; b] when b = a+1 -> Format.fprintf fmt "%s := int %d %d" info.Pr.id a b
    | _ -> failwith "Cannot support sparse domains at this stage."
  ) problem.Pr.ivals

let print_bvars fmt problem = 
  Dy.iter (fun info ->
    Format.fprintf fmt ",@ %s := int 0 1" (fst info)
  ) problem.Pr.bvals

let print_constraints fmt problem =
  Dy.iter (fun info ->
    Format.fprintf fmt ",@ " ;
    print_constraint fmt problem (fst (fst info)) (snd (fst info))) problem.Pr.constraints

let print_problem_cmodel fmt problem =
  Format.fprintf fmt "@[<v 1>[" ;
  Format.fprintf fmt "lit_True := int 1 1" ;
  print_ivars fmt problem ;
  print_bvars fmt problem ;
  print_constraints fmt problem ;
  Format.fprintf fmt "]@]@."

let main () =
  (* Parse the command-line arguments *)
  Arg.parse
    Opts.speclist
      (begin fun infile -> Opts.infile := Some infile end)
      "fzn_phage <options> <inputfile>"
  ;
  (* Parse the program *)
  let input = match !Opts.infile with
      | None -> stdin
      | Some file -> open_in file
  in
  (* Initialize printers *)
  init_printers () ;
  let lexer = P.lexer input in
  let problem = P.read_problem lexer in
  let out_fmt = match !Opts.outfile with
    | None -> Format.std_formatter
    | Some file ->
      let out_chan = open_out file in
      Format.formatter_of_out_channel out_chan in
  print_problem_cmodel out_fmt problem 

let _ = main ()
