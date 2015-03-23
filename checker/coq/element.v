Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import prim.
Require Import sol.
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
      (*
      ((satb_dbound (db_from_negclause i cl) k)
        && (satb_dbound (db_from_negclause x cl) y))
      *)
      && check_element_rec x i ys' cl
  end.
Definition check_element elem cl :=
  match elem with
  | Elem x i ys => check_element_rec x i (augment Z ys) cl
  end.

Theorem check_element_valid :
  forall (elem : element) (cl : clause),
    check_element elem cl = true ->
      implies (eval_element elem) (eval_clause cl).
Proof.
  unfold implies.
  unfold eval_element, check_element. destruct elem.
  generalize (augment Z l).
  intros l0 cl; induction l0.
  unfold eval_element_rec; tauto.

  unfold check_element_rec, eval_element_rec;
    fold check_element_rec; fold eval_element_rec.
  destruct a; simpl.
  rewrite andb_true_iff, negb_true_iff, andb_false_iff.
  intros.
  assert (eval_clause cl theta \/ ~eval_clause cl theta) as Hdec.
    tauto.
  destruct Hdec.
    exact H1.

    destruct H as [ Hf Hrec ].
    apply IHl0. exact Hrec.
    destruct H0.
    destruct H as [Hi0 Hi].
    rewrite satb_dom_false_iff_notdom in Hf.
    rewrite satb_dom_false_iff_notdom in Hf.
    destruct Hf.
        apply dom_from_negclause_valid with
          (x := i0) in H1.
        rewrite Hi0 in H1.
        tauto.

        apply dom_from_negclause_valid with
          (x := i) in H1.
        rewrite Hi in H1.
        tauto.
        exact H.
Qed.

Definition ElemConstraint : Constraint :=
  mkConstraint (element) (eval_element).
Definition ElemBnd := BoundedConstraint ElemConstraint.
Definition ElemCheck := mkChecker ElemConstraint (check_element) (check_element_valid).
Definition ElemBndCheck := BoundedChecker ElemConstraint ElemCheck.
Definition check_element_bnd (x : element) (bs : list (ivar*Z*Z)) (cl : clause) := 
  (check ElemBnd ElemBndCheck) (bs, x) cl.


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
Fixpoint eval_element_sol_rec x i ys theta :=
  match ys with
  | nil => false
  | cons (k, y) ys' =>
    (Z_eqb (eval_ivar i theta)  k) && (Z_eqb (eval_ivar x theta) y)
      || eval_element_sol_rec x i ys' theta
  end.

Definition eval_element_sol (con : element) (theta : asg) :=
  match con with
  | Elem x i ys => eval_element_sol_rec x i (augment Z ys) theta
  end.

Theorem eval_element_sol_rec_iff :
  forall x i ys theta,
    eval_element_sol_rec x i ys theta = true <-> eval_element_rec x i ys theta.
Proof.
  intros; induction ys; unfold eval_element_sol_rec, eval_element_rec;
    fold eval_element_sol_rec; fold eval_element_rec; simpl in *.

  split; intros; try congruence; try contradiction.

  destruct a; simpl in *.
  rewrite <- IHys.
  rewrite orb_true_iff; rewrite andb_true_iff.
  now  repeat (rewrite Z_eqb_iff_eq).
Qed.
Theorem eval_element_sol_valid :
    forall elt theta,
      (eval_element_sol elt theta = true) -> eval_element elt theta.
Proof.
  intros elt theta; unfold eval_element_sol, eval_element; destruct elt.
  now rewrite eval_element_sol_rec_iff.
Qed.

Definition ElementSolCheck := mkSolCheck ElemConstraint eval_element_sol eval_element_sol_valid.