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
(* let debug_print str = Format.fprintf err_fmt str *)
  
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

let check_inferences ?abort:(abort=false) model_info p_step =
  let (bs, csts) = Pr.model_of_model_info model_info in 
  let cst_map = C_impl.cst_map_of_csts csts in
  let ds = C_impl.domset_of_bounds bs in
  let hint = ref (-1) in
  let count = ref 0 in
  let not_fin = ref true in
  let okay = ref true in
  while !not_fin
  do
    incr count ;
    (* match Pr.parse_step model_info lmap toks *)
    try begin
      match p_step ()
      with
      | C_impl.Intro (id, cl) ->
          if not (C_impl.check_inference_domset ds cst_map !hint cl) then
            begin
              okay := false ;
              if abort then
                not_fin := false
              else
                () ;
              Format.fprintf fmt "Inference %d from c%d failed:@ " !count !hint ;
              Pr.print_clause fmt cl ;
              Format.fprintf fmt "@."
            end
      | C_impl.Hint h -> hint := h
      | C_impl.Resolve _ -> ()
      | C_impl.Del _ -> ()
    end with _ -> not_fin := false
  done ;
  !okay

(* let check_inferences_opt model_info obj k lmap toks = *)
let check_inferences_opt model_info obj k p_step =
  let (bs, csts) = Pr.model_of_model_info model_info in 
  let cst_map = C_impl.cst_map_of_csts csts in
  let ds = C_impl.domset_with_lt (C_impl.domset_of_bounds bs) obj k in
  let hint = ref (-1) in
  let okay = ref true in
  let not_end = ref true in
  (* *)
  let count = ref 0 in
  while !not_end
  do
    (* match Pr.parse_step model_info lmap toks *)
    incr count ;
    try
      begin
      match p_step ()
      with
      | C_impl.Intro (id, cl) ->
          if not (C_impl.check_inference_domset ds cst_map !hint cl) then
            begin
              okay := false ;
              not_end := false ;
              Format.fprintf fmt "Inference %d from c%d failed:@ " !count !hint ;
              Pr.print_clause fmt cl ;
              Format.fprintf fmt "@."
            end
      | C_impl.Hint h -> hint := h
      | C_impl.Resolve _ -> ()
      | C_impl.Del _ -> ()
      end
    with _ -> not_end := false
  done ;
  (* *)
  !okay

let check_no_resolve model_info sol obj p_step =
  (C_impl.certify_solution (Pr.model_of_model_info model_info) sol) &&
    (check_inferences_opt model_info obj (sol obj) p_step)

let check_resolution model_info p_step =
  let clause_db = H.create 17 in
  let okay = ref true in
  let not_fin = ref true in
  while !okay && !not_fin
  do
    (* match Pr.parse_step model_info lmap toks *)
    try begin
     match p_step ()
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
    end with _ -> not_fin := false
  done

let build_pstep model_info tchan =
  match !COption.litfile, !COption.bintrace with
  | Some lfile, true -> failwith "Warning: no support for Boolean binary traces"
  | None, true -> Bin_log.create model_info.Pr.ivars tchan
  | None, false -> Pr.parse_step_fd model_info (Spec.lexer (Stream.of_channel tchan))
  | Some lfile, false ->
    begin
      (* Read the literal semantics . *)
      debug_print "{Reading literals..." ;
      let lit_tokens = Spec.lexer (Stream.of_channel (open_in lfile)) in
      let lmap = Pr.parse_lit_map model_info lit_tokens in
      debug_print "done.}@." ;
      Pr.parse_step model_info lmap (Spec.lexer (Stream.of_channel tchan))
    end

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
      debug_print "{Reading solution..." ;
      let asg_toks = Spec.lexer (Stream.of_channel (open_in sf)) in
      let sol = Some (Pr.parse_solution model_info asg_toks) in
      debug_print "done }@." ;
      sol
  in
  (* Decide whether the literal semantics are inline or not. *)
  let model = Pr.model_of_model_info model_info in
  (*
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
  *)
  match (!COption.objective, opt_sol, !COption.tracefile) with
  | (Some ovar, Some sol, Some tfile) ->
    let tchannel = open_in tfile in
    (*
    let ttoks = (Spec.lexer (Stream.of_channel tchannel)) in
    let step0 = Pr.create (p_step ttoks) in
    *)
    let obj = Pr.get_ivar model_info ovar in
    let p_step = build_pstep model_info tchannel in
    let next_step = Pr.next in
    if !COption.no_resolve then
      begin
        let okay = check_no_resolve model_info sol obj p_step in
        if okay then
          Format.fprintf fmt "OKAY@."
        else
          Format.fprintf fmt "FAILED@."
      end
    else
      begin
        (* Format.fprintf fmt "Checking optimality...@." ; *)
        let step0 = Pr.create p_step in
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
      (* Format.fprintf fmt "Checking solution...@." ; *)
      let okay = C_impl.certify_solution model sol in
      if okay then
        Format.fprintf fmt "OKAY@."
      else
        Format.fprintf fmt "FAILED@."
    end
  | (_, _, Some tfile) ->
    begin
      let tchannel = open_in tfile in
      let p_step = build_pstep model_info tchannel in
      (* let ttoks = (Spec.lexer (Stream.of_channel tchannel)) in *)
      if !COption.debug then
        begin
          ignore (check_inferences ~abort:false model_info p_step) ;
          (* check_resolution model_info p_step  *)
        end
      else
        let okay =
          if !COption.no_resolve then
            check_inferences ~abort:true model_info p_step
          else
            begin
              let step0 = Pr.create p_step in
              let next_step = Pr.next in
              (* Format.fprintf fmt "Checking unsatisfiability...@." ; *)
              C_impl.certify_unsat model max_int step0 next_step
            end
        in
        if okay then
          Format.fprintf fmt "OKAY@."
        else
          Format.fprintf fmt "FAILED@."
    end
  | _ -> Format.fprintf fmt "ERROR: No solution or trace specified.@."

let _ = main () 
