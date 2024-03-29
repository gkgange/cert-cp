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
  | Element : ivar -> ivar -> list Z -> element.

Definition eval_element_alt con theta :=
  match con with
  | Element x i ys =>
    exists idx, (eval_ivar i theta) = Z.of_nat idx /\ nth_error ys idx = value (eval_ivar x theta) 
  end.

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
  | Element x i ys => eval_element_rec x i (augment Z ys) theta
  end.

(*
Lemma eval_element_alt_iff : forall con theta, eval_element con theta <-> eval_element_alt con theta.
Proof.
  intros con theta; destruct con; unfold eval_element, eval_element_alt; simpl in *.
  assert ((eval_ivar i0 theta) < 0 \/ 0 <= (eval_ivar i0 theta)). omega.

  destruct H; split; intros.
  destruct H0.
  assert (Hnn := Nat2Z.is_nonneg x).
  omega.

  unfold eval_element_rec in H0; induction l; simpl in *; [contradiction | fold eval_element_rec in *].
  unfold nth_error; simpl in *; fold nth_error.
  destruct H0; try omega.
  unfold augment in IHl.
  apply IHl in H0.
*)
  
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
  | Element x i ys => check_element_rec x i (augment Z ys) cl
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

Fixpoint eval_element_sol_rec x i ys theta :=
  match ys with
  | nil => false
  | cons (k, y) ys' =>
    (Z_eqb (eval_ivar i theta)  k) && (Z_eqb (eval_ivar x theta) y)
      || eval_element_sol_rec x i ys' theta
  end.

Definition eval_element_sol (con : element) (theta : asg) :=
  match con with
  | Element x i ys => eval_element_sol_rec x i (augment Z ys) theta
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
