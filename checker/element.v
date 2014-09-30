Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import prim.
Require Import bounds.

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
    (eval_ivar i theta = k /\ eval_ivar x theta = y)
      \/ eval_element_rec x i ys' (k+1) theta
  end.

Definition eval_element (con : element) (theta : asg) :=
  match con with
  | Elem x i ys => eval_element_rec x i ys 0 theta
  end.

Fixpoint check_element_rec x i ys k cl :=
  match ys with
  | nil => true
  | cons y ys' =>
    negb
      (inbounds_negcl cl i k && inbounds_negcl cl x y)
      && check_element_rec x i ys' (k+1) cl
  end.
Definition check_element elem cl :=
  match elem with
  | Elem x i ys => check_element_rec x i ys 0 cl
  end.

(*
Theorem check_element_rec_valid :
  forall (elt : element) (cl : clause),
  check_element elt cl = true ->
    implies (eval_element elt) (eval_clause cl).
Proof.
  unfold implies; destruct elt; intros.
  induction l.
Qed.
   
*)

