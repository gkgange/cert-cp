(* Top-level checker code. *)
module List = ExtLib.List
module A = DynArray
module L = List
module H = Hashtbl
module GL = Genlex
module MT = MTypes
module C = Checker
module Sol = SolCheck
module M = Model
module S = Spec
module P = Parse
module Pr = ProofState
module C_impl = Checker_impl

type ident = Pr.ident
type ivar = int

let ident_list = S.listof S.ident
let int_list = S.listof S.intconst

type arith =
  | Mul of (ivar * (ivar * ivar))
  | Div of (ivar * (ivar * ivar))

(* Boolean variables are just integers with range [0, 1]. *)
let print_list ?sep:(sep=";") f fmt xs =
  Format.fprintf fmt "[@[" ;
  begin
    match xs with
    | [] -> ()
    | (h :: tl) ->
      begin
        f fmt h ;
        List.iter (fun x ->
          Format.fprintf fmt "%s@ " sep ;
          f fmt x
        ) tl
      end
  end ;
  Format.fprintf fmt "]@]"

let emit_stream fmt f toks =
  Format.fprintf fmt "[@[" ;
  if Stream.peek toks <> None
  then
    begin
      (* Emit the first value *)
      f fmt toks ;
      while Stream.peek toks <> None
      do
        (* Emit the remaining values, separated by ';' *)
        Format.fprintf fmt ";@ " ;
        f fmt toks
      done
    end
  else
    () ;
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

 (*
let write_coq_vprop fmt v =
  match v with
  | C_impl.ILeq (x, k) -> Format.fprintf fmt "ILeq %d (%d)" x k
  | C_impl.IEq (x, k) -> Format.fprintf fmt "IEq %d (%d)" x k
  | C_impl.CTrue -> Format.fprintf fmt "CTrue"
  | _ -> ()

let write_coq_lit fmt l =
  match l with
  | C_impl.Pos v -> (Format.fprintf fmt "Pos (" ; write_coq_vprop fmt v; Format.fprintf fmt ")")
  | C_impl.Neg v -> (Format.fprintf fmt "Neg (" ; write_coq_vprop fmt v; Format.fprintf fmt ")")
*)
  
let parse_ilist =
  let rec aux ls = parser
    | [< 'GL.Int 0 >] -> List.rev ls
    | [< 'GL.Kwd "-" ; 'GL.Int k ; ret = aux ((-k) :: ls) >] -> ret
    | [< 'GL.Int k ; ret = aux (k :: ls) >] -> ret in
 fun toks -> aux [] toks

let emit_step fmt step =
  Format.pp_open_box fmt 2 ;
  begin
    match step with 
    | C_impl.Hint c -> Format.fprintf fmt "log.Hint@ (%d)" c
    | C_impl.Intro (id, cl) -> 
      begin
        Format.fprintf fmt "log.Intro %d@ " id ;
        Pr.print_clause fmt cl
        (* print_list write_coq_lit fmt cl *)
      end
    | C_impl.Resolve (id, cl, ants) ->
      begin
        Format.fprintf fmt "log.Resolve %d@ " id ;
        Pr.print_clause fmt cl ;
        (* print_list write_coq_lit fmt cl ; *)
        Format.fprintf fmt "@ " ;
        print_list Format.pp_print_int fmt ants
      end
    | C_impl.Del id -> Format.fprintf fmt "log.Del %d" id
  end ;
  Format.pp_close_box fmt ()
  
let parse_and_emit_steps fmt model lmap tokens =
  emit_stream fmt (fun fmt toks -> emit_step fmt (Pr.parse_step model lmap toks)) tokens

let parse_var_asg model = parser
  | [< 'GL.Ident v ; 'GL.Kwd "=" ; 'GL.Int k >] ->
      (M.get_ivar model v, k)

let parse_asg model tokens =
  chomp tokens (GL.Kwd "[") ;
  let asg = ref [] in
  while Stream.peek tokens <> Some (GL.Kwd "]")
  do
    asg := (parse_var_asg model tokens) :: !asg ;
    (if Stream.peek tokens = Some (GL.Kwd ",") then
      Stream.junk tokens)
  done ;
  List.rev !asg

let write_coq_tuple f fmt xs = print_list ~sep:"," f fmt xs

let write_lin fmt ks c =
  Format.fprintf fmt "model.Lin (" ;
  print_list (fun fmt (x, y) -> Format.fprintf fmt "(%d, %d)" x y) fmt ks ;
  Format.fprintf fmt ", %d)@;" c

let write_elem fmt x y ks =
  Format.fprintf fmt "model.Elem (element.Elem %d %d " x y ;
  print_list Format.pp_print_int fmt ks ;
  Format.fprintf fmt ")@;"

let write_cumul fmt c = 
  Format.fprintf fmt "@[model.Cumul@ (@[cumulative.mkCumul@ @[" ;
  print_list (fun fmt task ->
    Format.fprintf fmt "cumulative.mkTask %d %d %d@;"
      (C_impl.int_of_nat task.C_impl.duration) (C_impl.int_of_nat task.C_impl.resource) task.C_impl.svar
  ) fmt c.C_impl.tasks ;
  Format.fprintf fmt "@ %d)@]@]@]" (C_impl.int_of_nat c.C_impl.limit)

let write_clause fmt cl = 
  Format.fprintf fmt "model.Clause " ;
  (* print_list write_coq_lit fmt cl *)
  Pr.print_clause fmt cl
let write_arith fmt arith =
  Format.fprintf fmt "model.Arith <fix>"

let write_coq_cst fmt id cst =
  Format.fprintf fmt "@[(%d, " id ;
  begin
    match cst with
    | C_impl.Lin obj -> let (ts, k) = Obj.magic obj in write_lin fmt ts k
    | C_impl.Elem obj -> let (x, y, ks) = Obj.magic obj in write_elem fmt x y ks
    | C_impl.Cumul obj -> let c = Obj.magic obj in  write_cumul fmt c
    | C_impl.Clause obj -> let cs = Obj.magic obj in write_clause fmt cs
    | C_impl.Arith obj -> let arith = Obj.magic obj in write_arith fmt arith
    (*
    | C_impl.Lin (ts, k) -> write_lin fmt ts k 
    | C_impl.Elem (x, y, ks) -> write_elem fmt x y ks
    | C_impl.Cumul c -> write_cumul fmt c
    | C_impl.Clause cs -> write_clause fmt cs
    | C_impl.Arith arith -> write_arith fmt arith
    *)
  end ;
  Format.fprintf fmt ")@]"
    
let write_coq_csts fmt csts =
  Format.fprintf fmt "[@[" ;
  begin
    if A.length csts > 0 then
      begin
        write_coq_cst fmt 0 (A.get csts 0) ;
        for i = 1 to (A.length csts)-1 do
          Format.fprintf fmt ";@ " ;
          write_coq_cst fmt i (A.get csts i)
        done
      end
  end ;
  Format.fprintf fmt "]@]"
      
let write_bounds fmt bs =
  Format.fprintf fmt "@[[" ;
  let first = ref true in
  let aux i l u =
    begin
        if !first then
          first := false
        else
          Format.fprintf fmt ";@ "
    end ;
    Format.fprintf fmt "(%d, %d, %d)" i l u
  in
  for i = 0 to (A.length bs) - 1
  do
    match A.get bs i with
    | Some (l, u) -> aux i l u
    | None -> ()
  done ;
  Format.fprintf fmt "]@]"
  
let write_coq_model fmt ident model =
  Format.fprintf fmt "@[Definition %s_bounds@ :=@ @[" ident ;
  write_bounds fmt model.Pr.bounds ;
  Format.fprintf fmt ".@]@]@." ;
  Format.fprintf fmt "@[Definition %s_csts : model.csts@ :=@ " ident ;
  write_coq_csts fmt model.Pr.csts ;
  Format.fprintf fmt ".@]@." ;
  Format.fprintf fmt "@[Definition %s@ :=@ (%s_bounds, %s_csts).@]@." ident ident ident

let write_coq_proof fmt ident model lmap proof_toks =
  Format.fprintf fmt "@[Definition %s@ :=@ @[" ident ;
  parse_and_emit_steps fmt model lmap proof_toks ;
  Format.fprintf fmt ".@]@]@."

let write_prelude fmt =
  Format.fprintf fmt "Require Import prim.@." ;
  Format.fprintf fmt "Require bounds.@." ;
  Format.fprintf fmt "Require model.@." ;
  Format.fprintf fmt "Require log.@." ;
  Format.fprintf fmt "Require map.@." ;
  Format.fprintf fmt "Require Import List.@." ;
  Format.fprintf fmt "Require Import ZArith.@." ;
  Format.fprintf fmt "Import List.ListNotations.@." ;
  Format.fprintf fmt "Open Scope Z_scope.@."

let write_coq fmt model lmap proof_toks =
  write_prelude fmt ;
  write_coq_model fmt "p_model" model ; 
  write_coq_proof fmt "p_proof" model lmap proof_toks ;
  Format.fprintf fmt "Theorem model_unsat : model.model_unsat p_model.@." ;
  Format.fprintf fmt "Proof.@." ;
  Format.fprintf fmt "  apply log.certify_unsat_list_valid with (ss := p_proof)." ;
  Format.fprintf fmt "  now vm_compute.@." ;
  Format.fprintf fmt "Qed.@."
    
let main () =
  (* Parse the command-line arguments *)
  Arg.parse
    COption.speclist
      (begin fun infile -> COption.infile := Some infile end)
      "check_cp <options> <model_file>"
  ;
  (* Parse the model specification *)
  (*
  init_parsers () ;
  *)
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
  (*
  let opt_solution =
    match !COption.solfile with
    | None -> None
    | Some sf ->
        begin
          let asg_toks = Spec.lexer (Stream.of_channel (open_in sf)) in
          Some (parse_asg model asg_toks)
  end in
  *)
  (* Read the literal semantics . *)
  debug_print "{Reading literals..." ;
  let lit_tokens = match !COption.litfile with
    | None -> tokens
    | Some lfile -> Spec.lexer (Stream.of_channel (open_in lfile))
  in
  let lmap = Pr.parse_lit_map model lit_tokens in
  debug_print "done.}@." ;
  match !COption.tracefile with
  | None -> Format.fprintf fmt "ERROR: No trace specified@."
  | Some tfile ->
    begin
      debug_print "{Reading trace..." ;
      let tchannel = open_in tfile in
      (* let ttoks = Spec.lexer (Stream.of_channel tchannel) in *)
      let ttoks = (Spec.lexer (Stream.of_channel tchannel)) in
      write_coq fmt model lmap ttoks ;
      debug_print "done.}@."
    end

let _ = main () 
