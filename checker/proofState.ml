(* Implementation for working with Coq-level model *)
module C_impl = Checker_impl
module H = Hashtbl
module A = DynArray
module GL = Genlex
module S = Spec
module R = Registry

let fmt = Format.std_formatter
let err_fmt = Format.err_formatter
(* let debug_print str = Format.fprintf fmt str *)
let debug_print str = ()
  
let string_of_token = function
  | GL.Kwd s -> s
  | GL.Ident id -> id
  | GL.Int x -> string_of_int x
  | _ -> "<tok>"

type ident = string

type model_info = {
  ivars : (ident, int) H.t ;
  bounds : (int * int) option A.t ;
  cst_idxs : (ident, int) H.t ;
  csts : Checker_impl.cst A.t
}
  
let cst_parsers = H.create 17
let add_cst_parser = H.add cst_parsers

let get_cst_parser ident =
  try
    H.find cst_parsers ident
  with Not_found -> failwith (Format.sprintf "Unknown constraint: %s@." ident)
    
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

let ident_list = S.listof S.ident
let int_list = S.listof S.intconst
let ivar_list minfo toks = List.map (fun x -> get_ivar minfo x) (ident_list toks)

(* Constructing the model *)
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
        let pcst = (get_cst_parser key) in
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

let parse_model_info tokens =
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

(* Turn our model_info into extracted coq structures *)
let get_model_bounds minfo =
  let rec aux idx ss ts =
    match ts with
    | [] -> List.rev ss
    | (k :: ks) ->
      begin
        match k with
        | None -> aux (idx+1) ss ks
        | Some (l, u) -> aux (idx+1) ( ((idx, l), u) :: ss) ks
      end
  in aux 0 [] (A.to_list minfo.bounds)

let get_csts minfo = List.mapi (fun i cst -> (i, cst)) (A.to_list minfo.csts)

let model_of_model_info minfo = (get_model_bounds minfo, get_csts minfo)
  
(* Dealing with mapping of literal numbers to semantics *)
type literal_map = (int, Checker_impl.lit) H.t
let parse_vprop minfo =
  let aux ivar = parser
  | [< 'GL.Kwd "<=" ; 'GL.Int k >] -> C_impl.Pos (C_impl.ILeq (ivar, k))
  | [< 'GL.Kwd "=" ; 'GL.Int k >] -> C_impl.Pos (C_impl.IEq (ivar, k))
  | [< 'GL.Kwd ">=" ; 'GL.Int k >] -> C_impl.Neg (C_impl.ILeq (ivar, k-1))
  | [< 'GL.Kwd "!=" ; 'GL.Int k >] -> C_impl.Neg (C_impl.IEq (ivar, k))
  in parser
  | [< 'GL.Ident x ; prop = aux (get_ivar minfo x) >] -> prop
  | [< 'GL.Int k1 ; 'GL.Kwd "=" ; 'GL.Int k2 >] ->
      if k1 = k2 then C_impl.Pos C_impl.CTrue else C_impl.Neg C_impl.CTrue

let get_litsem model = parser
  | [< 'GL.Int v ; 'GL.Kwd "[" ; l = parse_vprop model ; 'GL.Kwd "]" >]
    -> (v, l)

let parse_lit_map model tokens =
  let lmap = H.create 3037 in
  while Stream.peek tokens <> None
  do
    let (v, l) = get_litsem model tokens in
    H.add lmap v l
  done ;
    lmap

type _proof_state =
| Open of (model_info * literal_map * Genlex.token Stream.t)
| Closed of (C_impl.step * (_proof_state ref)) option

type proof_state = _proof_state ref
type t = proof_state
  
 (*
let coq_lit_of_vprop v =
  match v with
  | MT.ILe (x, k) -> C_impl.Pos (C_impl.ILeq (x, k))
  | MT.IEq (x, k) -> C_impl.Pos (C_impl.IEq (x, k))
  | MT.BTrue x -> C_impl.Neg (C_impl.ILe (x, 0))
  | MT.CTrue -> C_impl.Pos C_impl.CTrue

let coq_lit_of_lit = function
  | MT.Pos v -> coq_lit_of_vprop v
  | MT.Neg v -> C_impl.neglit (coq_lit_of_vprop v)
 *)


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
      in C_impl.Hint idx
  | [< 'GL.Kwd "-" >] -> C_impl.Hint (-1)

let coqlits_of_ilist lmap ilist =
  List.map (fun i -> 
    if i > 0 then
      H.find lmap i
    else
      C_impl.neglit (H.find lmap (-i))
  ) ilist

let parse_inf model lmap = parser
  | [< 'GL.Ident "d" ; 'GL.Int cid >] -> C_impl.Del cid
  | [< 'GL.Ident "c" ; hint = parse_hint model >] -> hint
  | [< 'GL.Ident "h" ; hint = parse_hint model >] -> hint
  | [< 'GL.Int cid ; cl = parse_ilist ; ants = parse_ilist >] ->
      match ants with
      | [] -> C_impl.Intro (cid, coqlits_of_ilist lmap cl)
      | _ -> C_impl.Resolve (cid, coqlits_of_ilist lmap cl, ants)


let create info lmap toks = ref (Open (info, lmap, toks))
let parse_step info lmap toks = parse_inf info lmap toks
let next state =
  match !state with
  | Open (model, lmap, toks) ->
    let step = 
        if Stream.peek toks = None then
          None
        else
          Some ((parse_inf model lmap toks), ref (Open (model, lmap, toks)))
    in
    begin
      state := Closed step ;
      step
    end
  | Closed step -> step

(* Eagerly build a list of proof steps. *)
let parse_proof minfo lmap toks =
  let rec aux ss =
    if Stream.peek toks = None then
      List.rev ss
    else
      aux ((parse_inf minfo lmap toks) :: ss)
  in
  aux []
