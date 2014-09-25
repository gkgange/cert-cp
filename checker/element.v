Require Import ZArith.
Require Import Bool.
Require Import prim.
Require Import List.

(* Element constraint:
 * element x i [y_1, ..., y_n] <-> x = y_i.
 * 
 * We're assuming the elements are *)
Inductive element : Type :=
  | Elem : ivar -> ivar -> list Z -> element.

(* This is kind of an awkward definition. *)
Fixpoint eval_element_rec x i ys k theta :=
  match ys with
  | nil => False
  | cons y ys' =>
    (eval_ivar i theta = k /\ eval_ivar x theta = eval_ivar y theta)
      \/ eval_element_rec x i ys' (k+1) theta
  end.

Definition eval_element (con : element) (theta : asg) :=
  match con with
  | Elem x i ys => eval_element_rec x i ys 0 theta
  end.

