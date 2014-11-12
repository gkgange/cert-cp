Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import prim.
Require Import bounds.
Require Import domain.
Require Import domset.
Require Import element.
Require Import reif.

Fixpoint check_element_dfun_rec (x i : ivar) ys f :=
  match ys with
  | nil => true
  | cons (k, y) ys' =>
    negb
      ((satb_dom (f i) k)
        && (satb_dom (f x) y))
      && check_element_dfun_rec x i ys' f
  end.
Definition check_element_dfun elem f :=
  match elem with
  | Elem x i ys => check_element_dfun_rec x i (augment Z ys) f
  end.

Theorem check_element_dfun_rec_eq : forall (x i : ivar) ys cl f,
  is_negcl_domfun f cl -> check_element_dfun_rec x i ys f = check_element_rec x i ys cl.
Proof.
  intros.
  unfold is_negcl_domfun in H.
  induction ys.
  now unfold check_element_dfun_rec, check_element_rec.

  unfold check_element_dfun_rec, check_element_rec;
    simpl; fold check_element_dfun_rec; fold check_element_rec.
  destruct a; simpl.
  assert (forall x k, satb_dom (f x) k = satb_dom (dom_from_negclause x cl) k).
    intros.
    remember (satb_dom (f x0) k) as sf.
    remember (satb_dom (dom_from_negclause x0 cl) k) as sc.
    destruct sf, sc; try tauto; symmetry in Heqsf, Heqsc;
      try rewrite satb_dom_true_iff_dom in Heqsf;
      try rewrite satb_dom_false_iff_notdom in Heqsf;
      try rewrite satb_dom_true_iff_dom in Heqsc;
      try rewrite satb_dom_false_iff_notdom in Heqsc;
      assert (Heq := H x0 k); tauto.
    
    rewrite IHys.
    now repeat (rewrite <- H0).
Qed.

Theorem check_element_dfun_eq :
  forall (elem : element) (cl : clause) (f : domfun),
    is_negcl_domfun f cl ->
      check_element_dfun elem f = check_element elem cl.
Proof.
  intros; unfold check_element_dfun, check_element.
  destruct elem.
  now rewrite check_element_dfun_rec_eq with (cl := cl).
Qed.

Theorem check_element_dfun_valid : forall (elem : element) (f : domfun) (cl : clause),
  is_negcl_domfun f cl /\ check_element_dfun elem f = true ->
    implies (eval_element elem) (eval_clause cl).
Proof.
  intros; apply check_element_valid; destruct H;
  now rewrite <- check_element_dfun_eq with (f := f).
Qed.
  
Definition ElemDSet : DomCheck :=
  mkDomCheck (element) (eval_element) (check_element_dfun) (check_element_dfun_valid).

Definition ElemDomCheck : Constraint :=
  (CheckOfDomCheck (DomboundedCheck ElemDSet)). 

Definition check_elem_dbnd (e : element) (ds : domset) (cl : clause) :=
  (ElemDomCheck).(check) (ds, e) cl.

Definition check_reif_elem_dbnd (r : lit) (e : element) (ds : domset) (cl : clause) :=
  (ReifiedConstraint (ElemDomCheck)).(check) (r, (ds, e)) cl.