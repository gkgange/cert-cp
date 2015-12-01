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

type ident = MTypes.ident
type ivar = int

type linterm = (int * ivar)

type task = {
  duration : int ;
  resource : int ;
  svar : ivar 
}

type cumul = {
  tasks : task list ;
  limit : int
}

let ident_list = S.listof S.ident
let int_list = S.listof S.intconst

type arith =
  | Mul of (ivar * (ivar * ivar))
  | Div of (ivar * (ivar * ivar))

(* Boolean variables are just integers with range [0, 1]. *)
type coq_vprop =
| ILe of ivar*int
| IEq of ivar*int
| CTrue

type coq_lit =
| Pos of coq_vprop
| Neg of coq_vprop

let negate_coq_lit = function
  | Pos v -> Neg v
  | Neg v -> Pos v

let coq_lit_of_vprop v =
  match v with
  | MT.ILe (x, k) -> Pos (ILe (x, k))
  | MT.IEq (x, k) -> Pos (IEq (x, k))
  | MT.BTrue x -> Neg (ILe (x, 0))
  | MT.CTrue -> Pos CTrue

let coq_lit_of_lit = function
  | MT.Pos v -> coq_lit_of_vprop v
  | MT.Neg v -> negate_coq_lit (coq_lit_of_vprop v)

(* The closed set of constraints supported
 * by the full Coq-based checker. *)
type coq_cst =
  | Lin of ((linterm list) * int)
  | Elem of (ivar * ivar * int list)
  | Cumul of cumul
  | Clause of coq_lit list
  | Arith of arith

type coq_step =
  | Hint of int
  | Intro of int * (coq_lit list)
  | Derive of (int * (coq_lit list) * (int list))
  | Del of int

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

type model_info = {
  ivars : (ident, int) H.t ;
  bounds : (int * int) option A.t ;
  cst_idxs : (ident, int) H.t ;
  csts : coq_cst A.t
}

let create_model_info () = {
  ivars = H.create 17 ;
  bounds = A.create () ;
  cst_idxs = H.create 17 ;
  csts = A.create ()
}

let add_ivar m id opt_b =
  let idx = A.length m.bounds in
  begin
    H.add m.ivars id idx ;
    A.add m.bounds opt_b
  end

let get_ivar m id =
  try
    H.find m.ivars id
  with Not_found ->
    let idx = A.length m.bounds in
    begin
      H.add m.ivars id idx ;
      A.add m.bounds None ;
      idx
    end

let add_cst m id cst =
  let idx = A.length m.csts in
  begin
    H.add m.cst_idxs id idx ;
    A.add m.csts cst
  end
let ivar_list minfo toks = List.map (fun x -> get_ivar minfo x) (ident_list toks)

let (cst_parsers : (ident, (model_info -> Genlex.token Stream.t -> coq_cst)) H.t) = H.create 17

let add_parser id pfun = H.add cst_parsers id pfun

let parse_linear_le minfo toks =
  let (coeffs, (vars, k)) = (S.cons (S.listof S.intconst) (S.cons (S.listof S.ident) S.intconst)) toks in
  let linterms = List.map2 (fun c v -> (c, get_ivar minfo v)) coeffs vars in
  Lin (linterms, k)

let parse_elem minfo toks =
  let (x, (i, ys)) =
    (S.cons
      (S.ident)
      (S.cons S.ident int_list)) toks in
  Elem (get_ivar minfo x, get_ivar minfo i, ys)

let make_cumul xs durations resources lim =
  let rec mk_tasks ys ds rs = match ys with
    | [] -> []
    | (y :: yt) ->
        { duration = (List.hd ds) ;
          resource = (List.hd rs) ;
          svar = y
        } :: (mk_tasks yt (List.tl ds) (List.tl rs))
  in {
    tasks = mk_tasks xs durations resources ;
    limit = lim
  }

let parse_cumul minfo = parser
    | [< xs = ivar_list minfo ; 'Genlex.Kwd "," ; durations = int_list ;
          'Genlex.Kwd "," ; resources = int_list ;
          'Genlex.Kwd "," ; lim = S.intconst >] ->
            Cumul (make_cumul xs durations resources lim) 

let parse_clause minfo toks = failwith "parse_clause not implemented."

let init_parsers () =
  begin
    add_parser "linear_le" parse_linear_le ;
    add_parser "element" parse_elem ;
    add_parser "cumulative" parse_cumul ;
    add_parser "clause" parse_clause 
  end

(* constraint(id) |- clause *)
type inference = (MT.ident * MT.clause)

let fmt = Format.std_formatter
let err_fmt = Format.err_formatter
(* let debug_print str = Format.fprintf fmt str *)
let debug_print str = ()
  
let string_of_token = function
  | GL.Kwd s -> s
  | GL.Ident id -> id
  | GL.Int x -> string_of_int x
  | _ -> "<tok>"

let parse_vprop model =
  let aux ivar = parser
  | [< 'GL.Kwd "<=" ; 'GL.Int k >] -> MT.Pos (MT.ILe (ivar, k))
  | [< 'GL.Kwd "=" ; 'GL.Int k >] -> MT.Pos (MT.IEq (ivar, k))
  | [< 'GL.Kwd ">=" ; 'GL.Int k >] -> MT.Neg (MT.ILe (ivar, k-1))
  | [< 'GL.Kwd "!=" ; 'GL.Int k >] -> MT.Neg (MT.IEq (ivar, k))
  in parser
  | [< 'GL.Ident x ; prop = aux (get_ivar model x) >] -> prop
  | [< 'GL.Int k1 ; 'GL.Kwd "=" ; 'GL.Int k2 >] ->
      if k1 = k2 then MT.Pos MT.CTrue else MT.Neg MT.CTrue

let get_litsem model = parser
  | [< 'GL.Int v ; 'GL.Kwd "[" ; l = parse_vprop model ; 'GL.Kwd "]" >]
    -> (v, l)

(* Parsing code for definitions. *)
let parse_defn spec = parser
  | [< 'GL.Ident id ; 'GL.Kwd ":=" ; v = spec id >] -> v

(* Junk tokens until we hit a separator *)
let drop_defn toks =
  let should_junk = function
    | None -> false
    | Some (GL.Kwd ("," | "]")) -> false
    | _ -> true
  in
  while should_junk (Stream.peek toks)
  do
    Stream.junk toks
  done

let chomp tokens token =
  let next = Stream.next tokens in
  if next <> token then
    begin
      Format.fprintf fmt "Parse error: expected %s, got %s." (string_of_token token) (string_of_token next) ;
      failwith "Parse error"
    end

(* Determining the value of an identifier. *)
let term_defn model id =
  let aux key =
    match key with
    | "int" ->
       begin parser
         | [< 'GL.Int l ; 'GL.Int u >] -> add_ivar model id (Some (l,u))
         | [< >] -> add_ivar model id None
       end
    | "bool" ->
        begin parser
          | [< >] -> add_ivar model id (Some (0, 1))
        end
    | "prop" -> (fun toks -> drop_defn toks)
    | _ ->
      try
        let pcst = (H.find cst_parsers key) in
        fun tokens -> (
          (* Drop opening paren *)
          chomp tokens (GL.Kwd "(") ;
          (* Indirection is to support (eventually) providing
           * multiple checkers for a constraint. *)
          add_cst model id (pcst model tokens) ;
          (* Drop closing paren. *)
          chomp tokens (GL.Kwd ")") ;
        )
      with Not_found -> failwith (Format.sprintf "constraint not found: %s" key)
    in
  parser
    | [< 'GL.Ident key ; v = aux key >] -> v

let parse_model tokens =
  let model = create_model_info () in
  chomp tokens (GL.Kwd "[") ;
  if Stream.peek tokens <> (Some (GL.Kwd "]")) then
    begin
      parse_defn (term_defn model) tokens ;
      while Stream.peek tokens = Some (GL.Kwd ",") 
      do
        Stream.junk tokens ;
        parse_defn (term_defn model) tokens 
      done
    end ;
  chomp tokens (GL.Kwd "]") ;
  model

let coqlits_of_ilist lmap ilist =
  List.map (fun i -> 
    let l = 
        if i > 0 then
          H.find lmap i
        else
          MT.negate (H.find lmap (-i))
    in coq_lit_of_lit l
  ) ilist
    (*
type coq_vprop =
| ILe of ivar*int
| IEq of ivar*int

type coq_lit =
| Pos of coq_vprop
| Neg of coq_vprop
    *)

let write_coq_vprop fmt v =
  match v with
  | ILe (x, k) -> Format.fprintf fmt "ILeq %d (%d)" x k
  | IEq (x, k) -> Format.fprintf fmt "IEq %d (%d)" x k
  | CTrue -> Format.fprintf fmt "CTrue"

let write_coq_lit fmt l =
  match l with
  | Pos v -> (Format.fprintf fmt "Pos (" ; write_coq_vprop fmt v; Format.fprintf fmt ")")
  | Neg v -> (Format.fprintf fmt "Neg (" ; write_coq_vprop fmt v; Format.fprintf fmt ")")
  
let parse_ilist =
  let rec aux ls = parser
    | [< 'GL.Int 0 >] -> List.rev ls
    | [< 'GL.Kwd "-" ; 'GL.Int k ; ret = aux ((-k) :: ls) >] -> ret
    | [< 'GL.Int k ; ret = aux (k :: ls) >] -> ret in
 fun toks -> aux [] toks

let parse_hint model = parser
  | [< 'GL.Ident cname >] ->
      let idx =
        try
          H.find model.cst_idxs cname
        with Not_found -> (-1)
      in Hint idx
  | [< 'GL.Kwd "-" >] -> Hint (-1)

let parse_inf model lmap = parser
  | [< 'GL.Ident "d" ; 'GL.Int cid >] -> Del cid
  | [< 'GL.Ident "c" ; hint = parse_hint model >] -> hint
  | [< 'GL.Ident "h" ; hint = parse_hint model >] -> hint
  | [< 'GL.Int cid ; cl = parse_ilist ; ants = parse_ilist >] ->
      match ants with
      | [] -> Intro (cid, coqlits_of_ilist lmap cl)
      | _ -> Derive (cid, coqlits_of_ilist lmap cl, ants)

let parse_inferences model lmap tokens =
  let rec aux tl tokens =
    match Stream.peek tokens with
    | None -> List.rev tl
    | _ -> aux ((parse_inf model lmap tokens) :: tl) tokens
  in aux [] tokens

let emit_step fmt step =
  Format.pp_open_box fmt 2 ;
  begin
    match step with 
    | Hint c -> Format.fprintf fmt "log.Hint@ (%d)" c
    | Intro (id, cl) -> 
      begin
        Format.fprintf fmt "log.Intro %d@ " id ;
        print_list write_coq_lit fmt cl
      end
    | Derive (id, cl, ants) ->
      begin
        Format.fprintf fmt "log.Resolve %d@ " id ;
        print_list write_coq_lit fmt cl ;
        Format.fprintf fmt "@ " ;
        print_list Format.pp_print_int fmt ants
      end
    | Del id -> Format.fprintf fmt "log.Del %d" id
  end ;
  Format.pp_close_box fmt ()
  
let parse_and_emit_steps fmt model lmap tokens =
  emit_stream fmt (fun fmt toks -> emit_step fmt (parse_inf model lmap toks)) tokens

let parse_lmap model tokens =
  let lmap = H.create 3037 in
  while Stream.peek tokens <> None
  do
    let (v, l) = get_litsem model tokens in
    H.add lmap v l
  done ;
    lmap

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

let check_solution model sol =
  let sol_checks = M.get_sol_checkers model in
  List.for_all (fun c ->
    let okay = c.Sol.check sol in
    begin
      if not okay then
        Format.fprintf fmt "FAILED: %s" c.Sol.repr 
    end ;
    c.Sol.check sol
    ) sol_checks

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
      task.duration task.resource task.svar
  ) fmt c.tasks ;
  Format.fprintf fmt "@ %d)@]@]@]" c.limit

let write_clause fmt cl = 
  Format.fprintf fmt "model.Clause " ;
  print_list write_coq_lit fmt cl
let write_arith fmt arith =
  Format.fprintf fmt "model.Arith <fix>"

let write_coq_cst fmt id cst =
  Format.fprintf fmt "@[(%d, " id ;
  begin
    match cst with
    | Lin (ts, k) -> write_lin fmt ts k
    | Elem (x, y, ks) -> write_elem fmt x y ks
    | Cumul c -> write_cumul fmt c
    | Clause cs -> write_clause fmt cs
    | Arith arith -> write_arith fmt arith
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
  write_bounds fmt model.bounds ;
  Format.fprintf fmt ".@]@]@." ;
  Format.fprintf fmt "@[Definition %s_csts : model.csts@ :=@ " ident ;
  write_coq_csts fmt model.csts ;
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
  init_parsers () ;
  let model_channel = match !COption.infile with
      | None -> stdin
      | Some file -> open_in file
  in
  (* Register any additional checker modules. *)
  debug_print "{Reading model..." ;
  let tokens = Spec.lexer (Stream.of_channel model_channel) in 
  let model = parse_model tokens in
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
  let lmap = parse_lmap model lit_tokens in
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
