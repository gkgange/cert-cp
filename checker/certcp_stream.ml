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

let fmt = Format.std_formatter
let err_fmt = Format.err_formatter
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

let check_inferences model_info p_step toks =
  let model = Pr.model_of_model_info model_info in
  let hint = ref (-1) in
  let count = ref 0 in
  while Stream.peek toks <> None
  do
    incr count ;
    (* match Pr.parse_step model_info lmap toks *)
    match p_step toks
    with
    | C_impl.Intro (id, cl) ->
        if not (C_impl.check_inference_model model !hint cl) then
          begin
            Format.fprintf fmt "Inference %d from c%d failed:@ " !count !hint ;
            Pr.print_clause fmt cl ;
            Format.fprintf fmt "@."
          end
    | C_impl.Hint h -> hint := h
    | C_impl.Resolve _ -> ()
    | C_impl.Del _ -> ()
  done

(* let check_inferences_opt model_info obj k lmap toks = *)
let check_inferences_opt model_info obj k p_step toks =
  let (bs, csts) = Pr.model_of_model_info model_info in 
  let cst_map = C_impl.cst_map_of_csts csts in
  let ds = C_impl.domset_with_lt (C_impl.domset_of_bounds bs) obj k in
  let hint = ref (-1) in
  let okay = ref true in
  (* *)
  while !okay && Stream.peek toks <> None
  do
    (* match Pr.parse_step model_info lmap toks *)
    match p_step toks
    with
    | C_impl.Intro (id, cl) ->
        if not (C_impl.check_inference_domset ds cst_map !hint cl) then
          (okay := false; Format.fprintf fmt "Inference failed.@.")
    | C_impl.Hint h -> hint := h
    | C_impl.Resolve _ -> ()
    | C_impl.Del _ -> ()
  done ;
  (* *)
  !okay

let check_no_resolve model_info sol obj p_step toks =
  (C_impl.certify_solution (Pr.model_of_model_info model_info) sol) &&
    (check_inferences_opt model_info obj (sol obj) p_step toks)

let check_resolution model_info p_step toks =
  let clause_db = H.create 17 in
  let okay = ref true in
  while !okay && Stream.peek toks <> None
  do
    (* match Pr.parse_step model_info lmap toks *)
    match p_step toks
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
  (* Register constraint parsers *)
  Builtins.register () ;
  let model_channel = match !COption.infile with
      | None -> stdin
      | Some file -> open_in file
  in
  debug_print "{Reading model..." ;
  let tokens = Spec.lexer (Stream.of_channel model_channel) in 
  let model_info = Pr.parse_model_info tokens in
  debug_print "done.}@." ;
  (* Read the solution, if one provided. *)
  let opt_sol = match !COption.solfile with
    | None -> None
    | Some sf ->
      let asg_toks = Spec.lexer (Stream.of_channel (open_in sf)) in
      Some (Pr.parse_solution model_info asg_toks)
  in
  (* Decide whether the literal semantics are inline or not. *)
  let p_step =
    match !COption.litfile with
    | None -> Pr.parse_step_fd model_info
    | Some lfile ->
      begin
        (* Read the literal semantics . *)
        debug_print "{Reading literals..." ;
        let lit_tokens = Spec.lexer (Stream.of_channel (open_in lfile)) in
        let lmap = Pr.parse_lit_map model_info lit_tokens in
        debug_print "done.}@." ;
        Pr.parse_step model_info lmap
      end
  in
  let model = Pr.model_of_model_info model_info in
  match (!COption.objective, opt_sol, !COption.tracefile) with
  | (Some ovar, Some sol, Some tfile) ->
    let tchannel = open_in tfile in
    let ttoks = (Spec.lexer (Stream.of_channel tchannel)) in
    let obj = Pr.get_ivar model_info ovar in
    let step0 = Pr.create model_info p_step ttoks in
    let next_step = Pr.next in
    if !COption.no_resolve then
      begin
        let okay = check_no_resolve model_info sol obj p_step ttoks in
        if okay then
          Format.fprintf fmt "OKAY@."
        else
          Format.fprintf fmt "FAILED@."
      end
    else
      begin
        (* Format.fprintf fmt "Checking optimality...@." ; *)
        let okay = C_impl.certify_optimal model obj sol max_int step0 next_step in
        if okay then
          Format.fprintf fmt "OKAY@."
        else
          Format.fprintf fmt "FAILED@."
      end
  | (None, Some sol, Some tfile) ->
    Format.fprintf fmt "ERROR: Solution and trace provided, but no objective.@."
  | (_, Some sol, _) ->
    begin
      Format.fprintf fmt "Checking solution...@." ;
      let okay = C_impl.certify_solution model sol in
      if okay then
        Format.fprintf fmt "OKAY@."
      else
        Format.fprintf fmt "FAILED@."
    end
  | (_, _, Some tfile) ->
    begin
      let tchannel = open_in tfile in
      (* let ttoks = Spec.lexer (Stream.of_channel tchannel) in *)
      let ttoks = (Spec.lexer (Stream.of_channel tchannel)) in
      if !COption.debug then
        begin
          check_inferences model_info p_step ttoks ;
          check_resolution model_info p_step ttoks 
        end
      else
        begin
          let step0 = Pr.create model_info p_step ttoks in
          let next_step = Pr.next in
          (* Format.fprintf fmt "Checking unsatisfiability...@." ; *)
          let okay = C_impl.certify_unsat model max_int step0 next_step in
          if okay then
            Format.fprintf fmt "OKAY@."
          else
            Format.fprintf fmt "FAILED@."
        end
    end
  | _ -> Format.fprintf fmt "ERROR: No solution or trace specified.@."

let _ = main () 
