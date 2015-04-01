(* Type definitions for checkers. *)
module MT = MTypes

type solcheck = {
  (* For logging purposes. *)
  repr: string ;
  
  (* The actual check *)
  check: MT.assignment -> bool
}

type t = solcheck

let fail str = {
  repr = Format.sprintf "fail(%s)" str ;
  check = (fun asg -> false)
}

(* Function for building a checker from
 * a given type. *)
type 'a builder = 'a -> t
