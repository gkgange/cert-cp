Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import prim.
Require Import bounds.
Require Import domain.

(* Element constraint:
 * element x i [y_1, ..., y_n] <-> x = y_i.
 * 
 * We're assuming the elements are *)
Inductive element : Type :=
  | Elem : ivar -> ivar -> list Z -> element.

(* This is kind of an awkward definition. *)
Fixpoint eval_element_rec x i ys theta :=
  match ys with
  | nil => False
  | cons (k, y) ys' =>
    (eval_ivar i theta = k /\ eval_ivar x theta = y)
      \/ eval_element_rec x i ys' theta
  end.

Fixpoint augment_rec (A : Type) (xs : list A) (k : Z) :=
  match xs with
  | nil => nil
  | (cons x xs') => cons (k, x) (augment_rec A xs' (k+1))
  end.
Definition augment (A : Type) (xs : list A) :=
  augment_rec A xs 0.

Definition eval_element (con : element) (theta : asg) :=
  match con with
  | Elem x i ys => eval_element_rec x i (augment Z ys) theta
  end.

Fixpoint check_element_rec x i ys cl :=
  match ys with
  | nil => true
  | cons (k, y) ys' =>
    negb
      ((satb_dom (dom_from_negclause i cl) k)
        && (satb_dom (dom_from_negclause x cl) y))
      && check_element_rec x i ys' cl
  end.
Definition check_element elem cl :=
  match elem with
  | Elem x i ys => check_element_rec x i (augment Z ys) cl
  end.

(*
Theorem check_element_valid :
  forall (elem : element) (cl : clause) (theta : asg),
    check_element elem cl = true ->
      eval_element elem theta -> eval_clause cl theta.
Proof.
  unfold eval_element, check_element. destruct elem.
  generalize (augment Z l).
  intros l0 cl theta; induction l0.
  unfold eval_element_rec; tauto.

  unfold check_element_rec, eval_element_rec;
    fold check_element_rec; fold eval_element_rec.
  destruct a; simpl.
  rewrite andb_true_iff, negb_true_iff, andb_false_iff.
  intros.
  destruct H as [ Hf Hrec ].
  apply IHl0. exact Hrec.
  destruct H0.
*)
(*
Theorem check_element_valid :
  forall (elt : element) (cl : clause),
  check_element elt cl = true ->
    implies (eval_element elt) (eval_clause cl).
Proof.
  unfold implies, check_element, eval_element.
  intros elt cl; destruct elt.
  intros; induction l.
    unfold eval_element_rec in H0.
    tauto.

    unfold check_element_rec in H; fold check_element_rec in H.
    unfold eval_element_rec in H0; fold eval_element_rec in H0.
    apply andb_true_iff in H; destruct H as [Ha Hr].
    rewrite negb_true_iff in Ha.
    rewrite andb_false_iff in Ha.
    destruct H as apply andb_true_iff in H.

Qed.
   
*)

