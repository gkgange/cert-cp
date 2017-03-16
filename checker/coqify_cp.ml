(* Top-level checker code. *)
(* module List = ExtLib.List *)
module A = DynArray
module L = List
module H = Hashtbl
module GL = Genlex
module MT = MTypes
module S = Spec
module P = Parse
module Pr = ProofState
module C_impl = Checker_impl

open Utils

type ident = Pr.ident
type ivar = int

let ident_list = S.listof S.ident
let int_list = S.listof S.intconst

let parenthesize f fmt xs =
  Format.fprintf fmt "@[<hov 1>(" ;
  f fmt xs ;
  Format.fprintf fmt "@])"

(*
type arith =
  | Mul of (ivar * (ivar * ivar))
  | Div of (ivar * (ivar * ivar))
  *)

let iterm_str = function
  | C_impl.Ivar x -> Format.sprintf "(Ivar %d)" x
  | C_impl.Ilit k -> Format.sprintf "(Ilit %d)" k

let write_iterm fmt = function
  | C_impl.Ivar x -> Format.fprintf fmt "Ivar %d" x
  | C_impl.Ilit k -> Format.fprintf fmt "Ilit %d" k

let binop_str = function
  | C_impl.Plus -> "arith.Plus"
  | C_impl.Times -> "arith.Times"
  | C_impl.Sub -> "arith.Sub"
  | C_impl.Div -> "arith.Div"
  | C_impl.Min -> "arith.Min"
  | C_impl.Max -> "arith.Max"

let unop_str = function
  | C_impl.Abs -> "arith.Abs"
  | C_impl.Uminus -> "arith.Uminus"
 
let emit_stream fmt f =
  Format.fprintf fmt "[@[" ;
  begin
  try
    f fmt ;
    let okay = ref true in
    while !okay do
      (* Emit the remaining values, separated by ';' *)
      Format.fprintf fmt ";@ " ;
      try f fmt 
      with _ -> okay := false
    done
  with _ -> () 
  end ;
  Format.fprintf fmt "@]]@."

let fmt = Format.std_formatter
let err_fmt = Format.err_formatter
(* let debug_print str = Format.fprintf fmt str *)
let debug_print str = ()
  
let string_of_token = function
  | GL.Kwd s -> s
  | GL.Ident id -> id
  | GL.Int x -> string_of_int x
  | _ -> "<tok>"

let chomp tokens token =
  let next = Stream.next tokens in
  if next <> token then
    begin
      Format.fprintf fmt "Parse error: expected %s, got %s." (string_of_token token) (string_of_token next) ;
      failwith "Parse error"
    end

let emit_step fmt step =
  Format.pp_open_box fmt 2 ;
  begin
    match step with 
    | C_impl.Hint c -> Format.fprintf fmt "log.Hint@ (%d)" c
    | C_impl.Intro (id, cl) -> 
      begin
        Format.fprintf fmt "log.Intro %d@ " id ;
        Pr.print_clause fmt cl
      end
    | C_impl.Resolve (id, cl, ants) ->
      begin
        Format.fprintf fmt "log.Resolve %d@ " id ;
        Pr.print_clause fmt cl ;
        Format.fprintf fmt "@ " ;
        print_list Format.pp_print_int fmt ants
      end
    | C_impl.Del id -> Format.fprintf fmt "log.Del %d" id
  end ;
  Format.pp_close_box fmt ()
  
let parse_and_emit_steps fmt model p_step =
  emit_stream fmt (fun fmt -> emit_step fmt (p_step ()))

let parse_var_asg minfo = parser
  | [< 'GL.Ident v ; 'GL.Kwd "=" ; 'GL.Int k >] -> (Pr.get_ivar minfo v, k)

let parse_sol minfo tokens =
  let asg = S.listof (parse_var_asg minfo) tokens in
  asg

let write_coq_tuple f fmt xs = print_list ~sep:"," f fmt xs

let write_lin suff fmt ks c =
  Format.fprintf fmt "model.Lin%s (" suff ;
  print_list (fun fmt (x, y) -> Format.fprintf fmt "(%d, %s)" x (iterm_str y)) fmt ks ;
  Format.fprintf fmt ", %d)@;" c

let write_elem fmt x y ks =
  Format.fprintf fmt "model.Elem @[<hov 1>(element.Element %s %s " (iterm_str x) (iterm_str y) ;
  print_list write_iterm fmt ks ;
  Format.fprintf fmt "@])@;"

let write_cumul fmt c = 
  Format.fprintf fmt "@[model.Cumul@ @[<hov 1>(@[var_cumulative.mkCumul@ @[" ;
  print_list (fun fmt task ->
    Format.fprintf fmt "var_cumulative.mkTask %s %s %s@;"
      (iterm_str task.C_impl.duration)
      (iterm_str task.C_impl.resource)
      (iterm_str task.C_impl.svar)
  ) fmt c.C_impl.tasks ;
  Format.fprintf fmt "@ %s)@]@]@]@]" (iterm_str c.C_impl.limit)

let write_clause fmt cl = 
  Format.fprintf fmt "model.Clause " ;
  (* print_list write_coq_lit fmt cl *)
  Pr.print_clause fmt cl

let rec write_aexpr fmt exp =
  match exp with
  | C_impl.T t ->
    (Format.fprintf fmt "arith.T@ " ; parenthesize write_iterm fmt t)
  | C_impl.Op (op, e, f) ->
    begin
      Format.fprintf fmt "arith.Op@ %s@ @[<hov 1>(" (binop_str op) ;
      write_aexpr fmt e ;
      Format.fprintf fmt "@])@ @[<hov 1>(" ;
      write_aexpr fmt f ;
      Format.fprintf fmt "@])"
    end
  | C_impl.Un (op, e) ->
    begin
      Format.fprintf fmt "arith.Un@ %s@ " (unop_str op) ;
      parenthesize write_aexpr fmt e
    end

let write_arith suff fmt arith =
  Format.fprintf fmt "model.Arith%s@[<hov 1>(" suff ;
  write_iterm fmt (fst arith) ;
  Format.fprintf fmt ",@," ;
  write_aexpr fmt (snd arith) ;
  Format.fprintf fmt "@])@;"

let write_memb ident fmt x ks =
  Format.fprintf fmt "%s@[<hov 1>(" ident ;
  write_iterm fmt x ;
  Format.fprintf fmt ",@," ;
  print_list write_iterm fmt ks ; 
  Format.fprintf fmt "@])@;"

let rec write_cst_body fmt cst =
  match cst with
  | C_impl.Lin obj -> let (ts, k) = Obj.magic obj in write_lin "" fmt ts k
  | C_impl.LinNE obj -> let (ts, k) = Obj.magic obj in write_lin "NE" fmt ts k
  | C_impl.Elem obj -> let (x, y, ks) = Obj.magic obj in write_elem fmt x y ks
  | C_impl.Memb obj -> let (x, vs) = Obj.magic obj in write_memb "model.Memb" fmt x vs
  | C_impl.Notmem0 obj -> let (x, vs) = Obj.magic obj in write_memb "model.Notmem" fmt x vs
  | C_impl.Cumul obj -> let c = Obj.magic obj in  write_cumul fmt c
  | C_impl.Clause obj -> let cs = Obj.magic obj in write_clause fmt cs
  | C_impl.Arith obj -> let arith = Obj.magic obj in write_arith "" fmt arith
  | C_impl.ArithNE obj -> let arith = Obj.magic obj in write_arith "NE" fmt arith
  | C_impl.Conj (x, y) -> write_meta fmt "model.Conj" [x; y]
  | C_impl.Disj (x, y) -> write_meta fmt "model.Disj" [x; y]
  | C_impl.Half (r, c) -> write_half fmt r c
  | C_impl.Tauto -> ()
and write_meta fmt ident args =
  Format.fprintf fmt "%s@[<hov 1>@ " ident ;
  Utils.print_list ~pre:"" ~post:"" ~sep:"@ " (parenthesize write_cst_body) fmt args ;
  Format.fprintf fmt "@]"
and write_half fmt lit cst =
  Format.fprintf fmt "model.Half@[<hov 1>@ " ; 
  parenthesize Pr.print_lit fmt lit ;
  Format.fprintf fmt "@ " ;
  parenthesize write_cst_body fmt cst ;
  Format.fprintf fmt "@]" 

let write_coq_cst fmt id cst =
  Format.fprintf fmt "@[(%d, " id ;
  write_cst_body fmt cst ;
  Format.fprintf fmt ")@]"
    
(* Bundle each cst with its index, then print *)
let write_coq_csts fmt csts =
  A.to_list csts |> List.mapi (fun i b -> (i, b)) |> 
    Utils.print_list (fun fmt (i, c) -> write_coq_cst fmt i c) fmt
  (*
  Utils.print_enum (fun fmt (i, c) -> write_coq_cst fmt i c) fmt
    @@ Enum.mapi (fun i b -> (i, b)) @@ A.enum csts
    *)
      
(* Bundle bounds with the corresponding index, remove missing bounds, then print. *)
let filter_map f xs =
  let rec aux xs acc =
    match xs with
    | [] -> List.rev acc
    | x :: xs' ->
    begin
      match f x with
      | None -> aux xs' acc
      | Some y -> aux xs' (y :: acc)
    end
  in
  aux xs []

let write_bounds fmt bs =
  let print_tuple = (fun fmt (i, l, u) -> Format.fprintf fmt "(%d, (%d, %d))" i l u) in
  let flatten (i, b) = match b with
    | None -> None
    | Some (l, u) -> Some (i, l, u)
  in
  (*
  A.enum bs |> Enum.mapi (fun i b -> (i, b)) |> Enum.filter_map flatten |> Utils.print_enum print_tuple fmt
  *)
  A.to_list bs |> List.mapi (fun i b -> (i, b)) |> filter_map flatten |> Utils.print_list print_tuple fmt
  
let write_coq_model fmt ident model =
  Format.fprintf fmt "@[Definition %s_bounds@ :=@ @[" ident ;
  write_bounds fmt model.Pr.bounds ;
  Format.fprintf fmt ".@]@]@." ;
  Format.fprintf fmt "@[Definition %s_csts : model.csts@ :=@ " ident ;
  write_coq_csts fmt model.Pr.csts ;
  Format.fprintf fmt ".@]@." ;
  Format.fprintf fmt "@[Definition %s@ :=@ (%s_bounds, %s_csts).@]@." ident ident ident

let write_coq_proof fmt ident model p_step =
  Format.fprintf fmt "@[Definition %s@ :=@ @[" ident ;
  parse_and_emit_steps fmt model p_step ;
  Format.fprintf fmt ".@]@]@."

let write_prelude fmt =
  (* Format.fprintf fmt "Require Import prim.@." ; *)
  Format.fprintf fmt "Require Import assign.@." ;
  Format.fprintf fmt "Require Import lit.@." ;
  Format.fprintf fmt "Require Import model.@." ;
  Format.fprintf fmt "Require log.@." ;
  Format.fprintf fmt "Require map.@." ;
  Format.fprintf fmt "Require Import List.@." ;
  Format.fprintf fmt "Require Import ZArith.@." ;
  Format.fprintf fmt "Import List.ListNotations.@." ;
  Format.fprintf fmt "Open Scope Z_scope.@."

let write_unsat_theorem fmt model_id proof_id =
  Format.fprintf fmt "Theorem model_unsat : model.model_unsat %s.@." model_id;
  Format.fprintf fmt "Proof.@." ;
  Format.fprintf fmt "  apply log.certify_unsat_list_valid with (p_proof := %s)." proof_id ;
  Format.fprintf fmt "  now vm_compute.@." ;
  Format.fprintf fmt "Qed.@."

let write_sol_theorem fmt model_id sol_id =
  Format.fprintf fmt "Theorem model_solution : model.eval_model %s %s.@." model_id sol_id;
  Format.fprintf fmt "Proof.@." ;
  Format.fprintf fmt "  apply log.certify_solution_valid.@." ;
  Format.fprintf fmt "  now vm_compute.@." ;
  Format.fprintf fmt "Qed.@."

let write_opt_theorem fmt model_id obj sol_id proof_id =
  Format.fprintf fmt "Theorem model_opt : model.is_model_minimum %s %d %s.@." model_id obj sol_id;
  Format.fprintf fmt "Proof.@." ;
  Format.fprintf fmt "  apply log.certify_optimal_list_valid with (p_proof := %s)." proof_id ;
  Format.fprintf fmt "  now vm_compute.@." ;
  Format.fprintf fmt "Qed.@."

let write_coq_sol fmt sol_id sol =
  Format.fprintf fmt "Definition %s := log.asg_of_alist " sol_id ;
  print_list (fun fmt (x, k) -> Format.fprintf fmt "(%d, (%d))" x k) fmt sol ;
  Format.fprintf fmt ".@."
(*
let write_coq fmt model lmap proof_toks =
  write_prelude fmt ;
  write_coq_model fmt "p_model" model ; 
  write_coq_proof fmt "p_proof" model lmap proof_toks ;
  write_unsat_theorem "p_model" "p_proof"
  *)
    
let write_coq fmt model opt_obj opt_sol opt_trace =
  write_prelude fmt ;
  write_coq_model fmt "p_model" model ;
  match (opt_obj, opt_sol, opt_trace) with
  | (Some obj, Some sol, Some p_step) ->
      begin
        write_coq_sol fmt "p_solution" sol ;
        write_coq_proof fmt "p_proof" model p_step ;
        write_opt_theorem fmt "p_model" obj "p_solution" "p_proof"
      end
  | (None, Some _, Some _) ->
      Format.fprintf err_fmt "ERROR: Solution and trace provided, but no objective.@."
  | (_, Some sol, _) ->
      begin
        write_coq_sol fmt "p_solution" sol ;
        write_sol_theorem fmt "p_model" "p_solution"
      end
  | (_, _, Some p_step) ->
      begin
        write_coq_proof fmt "p_proof" model p_step ;
        write_unsat_theorem fmt "p_model" "p_proof"
      end
  | _ -> ()

let main () =
  (* Parse the command-line arguments *)
  Arg.parse
    COption.speclist
      (begin fun infile -> COption.infile := Some infile end)
      "check_cp <options> <model_file>"
  ;
  (* Parse the model specification *)
  Builtins.register () ;
  let model_channel = match !COption.infile with
      | None -> stdin
      | Some file -> open_in file
  in
  (* Register any additional checker modules. *)
  debug_print "{Reading model..." ;
  let tokens = Spec.lexer (Stream.of_channel model_channel) in 
  let model = Pr.parse_model_info tokens in
  debug_print "done.}@." ;
  (* Read the solution, if one provided. *)
  let opt_sol =
    match !COption.solfile with
    | None -> None
    | Some sf ->
        begin
          let asg_toks = Spec.lexer (Stream.of_channel (open_in sf)) in
          Some (parse_sol model asg_toks)
  end in
  let opt_trace =
    match !COption.tracefile with
    | Some tfile ->
        begin
          let ttoks = (Spec.lexer (Stream.of_channel (open_in tfile))) in
          (* Read the literal semantics . *)
          let p_step = match !COption.litfile with
            | None -> Pr.parse_step_fd model ttoks
            | Some lfile ->
              begin
                debug_print "{Reading literals..." ;
                let lit_tokens =
                      Spec.lexer (Stream.of_channel (open_in lfile)) in
                let lmap = Pr.parse_lit_map model lit_tokens in
                debug_print "done.}@." ;
                Pr.parse_step model lmap ttoks
              end
          in Some p_step
        end
    | _ -> None
  in
  let opt_obj =
    match !COption.objective with
    | Some v -> Some (Pr.get_ivar model v)
    | _ -> None
  in
  write_coq fmt model opt_obj opt_sol opt_trace

let _ = main () 
