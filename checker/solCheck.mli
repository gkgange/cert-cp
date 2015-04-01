(* Type definitions for checkers. *)
type solcheck = {
  (* For logging purposes. *)
  repr: string ;
  
  (* The actual check *)
  check: MTypes.assignment -> bool
} 

val fail : string -> solcheck

type t = solcheck

(* Function for building a checker from
 * a given type. *)
type 'a builder = 'a -> t
