(* Type definitions for checkers. *)
type checker = {
  (* For logging purposes. *)
  repr: string ;
  
  (* The actual check *)
  check: MTypes.clause -> bool
} 

type t = checker

(* Function for building a checker from
 * a given type. *)
type 'a builder = 'a -> t
