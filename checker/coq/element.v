Require Import ZArith.
Require Import Bool.
Require Import assign.
Require Import domain.
Require Import range.
Require Import range_properties.
Require Import constraint.

(* Element constraint:
 * element x i [y_1, ..., y_n] <-> x = y_i.
 * 
 * We're assuming the elements are *)
Inductive element : Type :=
  | Element : ivar -> ivar -> list Z -> element.

(*
Definition eval_element_alt con theta :=
  match con with
  | Element x i ys =>
    exists idx, (theta i) = Z.of_nat idx /\ nth_error ys idx = value (theta x) 
  end.
*)

(* This is kind of an awkward definition. *)
Fixpoint eval_element_rec (x : ivar) (i : ivar) (ys : list (Z * Z)) theta :=
  match ys with
  | nil => False
  | cons (k, y) ys' =>
    (theta i = k /\ theta x = y)
      \/ eval_element_rec x i ys' theta
  end.

Fixpoint augment_rec (A : Type) (xs : list A) (k : Z) :=
  match xs with
  | nil => nil
  | (cons x xs') => cons (k, x) (augment_rec A xs' (k+1))
  end.
Definition augment (A : Type) (xs : list A) :=
  augment_rec A xs 0.

Definition eval_element (con : element) (theta : valuation) :=
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
  
Fixpoint check_element_rec x i ys ds :=
  match ys with
  | nil => true
  | cons (k, y) ys' =>
    negb
      ((satb_dom (var_dom ds i) k)
        && (satb_dom (var_dom ds x) y))
      (*
      ((satb_dbound (db_from_negclause i cl) k)
        && (satb_dbound (db_from_negclause x cl) y))
      *)
      && check_element_rec x i ys' ds
  end.

Definition ElemConstraint : Constraint :=
  mkConstraint (element) (eval_element).

Definition check_element_unsat elem ds :=
  match elem with
  | Element x i ys => check_element_rec x i (augment Z ys) ds
  end.

Theorem check_element_unsat_valid : forall (elem : element) (ds : domset),
    check_element_unsat elem ds = true -> cst_is_unsat ElemConstraint elem ds.
Proof.
  unfold cst_is_unsat, eval.
  unfold ElemConstraint, eval_element, check_element_unsat; destruct elem.
  generalize (augment Z l); intros l0 ds; induction l0.

  intros; unfold eval_element_rec in H1; contradiction.

  unfold check_element_rec, eval_element_rec, augment, augment_rec in *;
    fold augment_rec in *; fold check_element_rec in *; fold eval_element_rec in *.
  destruct a; simpl.
  rewrite andb_true_iff, negb_true_iff, andb_false_iff in *.
  intros.
  destruct H.

  destruct H1; [destruct H1 as [Hi0 Hi] | apply IHl0 with (theta := theta) in H2].

    destruct H; [apply (eval_domset_vardom ds i0) in H0 | apply (eval_domset_vardom ds i) in H0];
      unfold eval_dom in H0; simpl in H0; [rewrite Hi0 in H0 | rewrite Hi in H0];
      apply satb_dom_iff in H0; congruence.

    contradiction.
    assumption.
    assumption.
Qed.

Definition ElemCheckUnsat := mkUnsatChecker ElemConstraint (check_element_unsat) (check_element_unsat_valid).

Fixpoint eval_element_sol_rec (x : ivar) (i : ivar) ys (theta : valuation) :=
  match ys with
  | nil => false
  | cons (k, y) ys' =>
    (Z.eqb (theta i)  k) && (Z.eqb (theta x) y)
      || eval_element_sol_rec x i ys' theta
  end.

Definition eval_element_sol (con : element) (theta : valuation) :=
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
  now  repeat (rewrite Z.eqb_eq).
Qed.
Theorem eval_element_sol_valid :
    forall elt theta,
      (eval_element_sol elt theta = true) -> eval_element elt theta.
Proof.
  intros elt theta; unfold eval_element_sol, eval_element; destruct elt.
  now rewrite eval_element_sol_rec_iff.
Qed.

Definition ElementSolCheck := mkSolChecker ElemConstraint eval_element_sol eval_element_sol_valid.
