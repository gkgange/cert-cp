(* Top-level checker code. *)
module List = ExtLib.List
module A = DynArray
module L = List
module H = Hashtbl
module GL = Genlex
module MT = MTypes
module S = Spec
module P = Parse
module Pr = ProofState
module C_impl = Checker_impl

type ident = Pr.ident
type ivar = int

let ident_list = S.listof S.ident
let int_list = S.listof S.intconst

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

let parse_ilist =
  let rec aux ls = parser
    | [< 'GL.Int 0 >] -> List.rev ls
    | [< 'GL.Kwd "-" ; 'GL.Int k ; ret = aux ((-k) :: ls) >] -> ret
    | [< 'GL.Int k ; ret = aux (k :: ls) >] -> ret in
 fun toks -> aux [] toks

(*
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
  *)

let check_inferences model_info lmap toks =
  let model = Pr.model_of_model_info model_info in
  let hint = ref (-1) in
  while Stream.peek toks <> None
  do
    match Pr.parse_step model_info lmap toks
    with
    | C_impl.Intro (id, cl) ->
        if not (C_impl.check_inference_model model !hint cl) then
          Format.fprintf fmt "Inference failed.@."
    | C_impl.Hint h -> hint := h
    | C_impl.Resolve _ -> ()
    | C_impl.Del _ -> ()
  done

let check_resolution model_info lmap toks =
  let clause_db = H.create 17 in
  let okay = ref true in
  while !okay && Stream.peek toks <> None
  do
    match Pr.parse_step model_info lmap toks
    with
    | C_impl.Intro (id, cl) -> H.add clause_db id cl
    | C_impl.Hint _ -> ()
    | C_impl.Resolve (id, cl, ant_ids) ->
      let ants = List.rev @@ List.map (H.find clause_db) ant_ids in
      if not (C_impl.resolvable cl ants) then
        begin
          Format.fprintf fmt "@[Resolution failure:@ %d@ " id ;
          Pr.print_clause fmt cl ;
          Format.fprintf fmt "@ -/|@ " ;
          print_list Format.pp_print_int fmt ant_ids ;
          Format.fprintf fmt "@]@." ;
          Format.open_box 2 ;
          print_list Pr.print_clause fmt ants ;
          Format.fprintf fmt "@]@.";
          okay := false
        end
      else
        H.add clause_db id cl
    | C_impl.Del id -> H.remove clause_db id
  done

let main () =
  (* Parse the command-line arguments *)
  Arg.parse
    COption.speclist
      (begin fun infile -> COption.infile := Some infile end)
      "check_cp <options> <model_file>"
  ;
  (* Parse the model specification *)
  (* Builtins.register () ; *)
  let model_channel = match !COption.infile with
      | None -> stdin
      | Some file -> open_in file
  in
  (* Register any additional checker modules. *)
  debug_print "{Reading model..." ;
  let tokens = Spec.lexer (Stream.of_channel model_channel) in 
  let model_info = Pr.parse_model_info tokens in
  (* let model = Pr.model_of_model_info model_info in *)
  debug_print "done.}@." ;
  (* Read the solution, if one provided. *)
  let opt_sol = match !COption.solfile with
    | None -> None
    | Some sf ->
      let asg_toks = Spec.lexer (Stream.of_channel (open_in sf)) in
      Some (Pr.parse_solution model_info asg_toks)
  in
  (* Read the literal semantics . *)
  debug_print "{Reading literals..." ;
  let lit_tokens = match !COption.litfile with
    | None -> tokens
    | Some lfile -> Spec.lexer (Stream.of_channel (open_in lfile))
  in
  let lmap = Pr.parse_lit_map model_info lit_tokens in
  debug_print "done.}@." ;
  let model = Pr.model_of_model_info model_info in
  match (!COption.objective, opt_sol, !COption.tracefile) with
  | (Some ovar, Some sol, Some tfile) ->
    let tchannel = open_in tfile in
    let ttoks = (Spec.lexer (Stream.of_channel tchannel)) in
    let obj = Pr.get_ivar model_info ovar in
    let step0 = Pr.create model_info lmap ttoks in
    let next_step = Pr.next in
    begin
      Format.fprintf fmt "Checking optimality...@." ;
      let okay = C_impl.certify_optimal model obj sol max_int step0 next_step in
      if okay then
        Format.fprintf fmt "@ successful.@."
      else
        Format.fprintf fmt "@ failed.@."
    end
  | (None, Some sol, Some tfile) ->
    Format.fprintf fmt "ERROR: Solution and trace provided, but no objective.@."
  | (_, Some sol, _) ->
    begin
      Format.fprintf fmt "Checking solution...@." ;
      let okay = C_impl.certify_solution model sol in
      if okay then
        Format.fprintf fmt "@ successful.@."
      else
        Format.fprintf fmt "@ failed.@."
    end
  | (_, _, Some tfile) ->
    begin
      let tchannel = open_in tfile in
      (* let ttoks = Spec.lexer (Stream.of_channel tchannel) in *)
      let ttoks = (Spec.lexer (Stream.of_channel tchannel)) in
      (* check_inferences model_info lmap ttoks *)
      (* check_resolution model_info lmap ttoks *)
      (* *)
      let step0 = Pr.create model_info lmap ttoks in
      let next_step = Pr.next in
      Format.fprintf fmt "Checking unsatisfiability...@." ;
      let okay = C_impl.certify_unsat model max_int step0 next_step in
      if okay then
        Format.fprintf fmt "@ successful.@."
      else
        Format.fprintf fmt "@ failed.@."
    end
  | _ -> Format.fprintf fmt "ERROR: No solution or trace specified.@."

let _ = main () 
