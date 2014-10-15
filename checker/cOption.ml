(* Option handling *)
let infile = ref None
let modules = ref []

let verbosity = ref 0

let stream = ref false

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
    ]
