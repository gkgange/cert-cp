(* Type definitions for checkers. *)
module MT = MTypes

type checker = {
  (* For logging purposes. *)
  repr: string ;
  
  (* The actual check *)
  check: MT.clause -> bool
} 

type t = checker

(* Function for building a checker from
 * a given type. *)
type 'a builder = 'a -> t
