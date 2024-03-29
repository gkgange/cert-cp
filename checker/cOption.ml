(* Option handling *)
let infile = ref None
let modules = ref []
let tracefile = ref None
let bintrace = ref false
let litfile = ref None
let solfile = ref None
let objective = ref None

let verbosity = ref 0

let stream = ref false
let no_resolve = ref false
let debug = ref false

type trace_kind =
  | IDrup (* DRUP with axiom introduction. *)
  | Dres (* Resolution proof with deletion *)

let tracemode = ref IDrup
(* --------------------------------------------- *)
(*       Specification list for options          *)
(* --------------------------------------------- *)
let (speclist:(Arg.key * Arg.spec * Arg.doc) list) =
  Arg.align
    [(
      "-verbosity",
      Arg.Set_int(verbosity),
      "<int> verbosity level, from 0 to 2 (default:0)"
     ) ;
     (
       "-load",
       Arg.String(fun m -> modules := m :: !modules),
       "<string> additional checker module to load."
     ) ;
     ("-stream",
      Arg.Unit(fun () -> stream := true),
      " avoid storing inferences; check them immediately on reading."
     ) ;
     ("-no-resolve",
      Arg.Unit (fun () -> no_resolve := true),
      " check inferences, but not resolution steps."
     ) ;
     ("-trace",
      Arg.String(fun f -> tracefile := Some f),
      " resolution proof trace to attempt to justify."
     );
     ("-bintrace",
      Arg.Unit (fun f -> bintrace := true),
      " read a binary (rather than text) proof trace."
     );
     ("-debug",
      Arg.Unit (fun () -> debug := true),
      " try to identify a failed inference/resolution step.");
     ("-format",
       Arg.Symbol([ "idrup" ; "dres" ], fun m ->
         match m with
         | "idrup" -> tracemode := IDrup
         | "dres" -> tracemode := Dres),
       " format of resolution trace."
     );
     ("-lits",
      Arg.String(fun f -> litfile := Some f),
      " mapping of trace literals to model semantics."
     );
     ("-objective",
      Arg.String(fun s -> objective := Some s),
      " variable to minimize."
     );
     ("-solution",
      Arg.String(fun f -> solfile := Some f),
      " claimed solution to check."
     )
    ]
