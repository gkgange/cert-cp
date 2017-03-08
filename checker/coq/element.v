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
  | Element : iterm -> iterm -> list iterm -> element.

(*
Definition eval_element_alt con theta :=
  match con with
  | Element x i ys =>
    exists idx, (theta i) = Z.of_nat idx /\ nth_error ys idx = value (theta x) 
  end.
*)

(* This is kind of an awkward definition. *)
Fixpoint eval_element_rec (x : iterm) (i : iterm) (ys : list (Z * iterm)) theta :=
  match ys with
  | nil => False
  | cons (k, y) ys' =>
    ((eval_iterm i theta) = k /\ (eval_iterm x theta)  = (eval_iterm y theta))
      \/ eval_element_rec x i ys' theta
  end.

Fixpoint augment_rec (A : Type) (xs : list A) (k : Z) :=
  match xs with
  | nil => nil
  | (cons x xs') => cons (k, x) (augment_rec A xs' (k+1))
  end.
Definition augment (A : Type) (xs : list A) :=
  augment_rec A xs 1.

Definition eval_element (con : element) (theta : valuation) :=
  match con with
  | Element x i ys => eval_element_rec x i (augment _ ys) theta
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
    (*
    negb
      ((satb_dom (var_dom ds i) k)
        && (satb_dom (var_dom ds x) y))
     *)
    ((negb (satb_dom (term_dom ds i) k))
         || (dom_unsatb (dom_meet (term_dom ds x) (term_dom ds y))))
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
  | Element x i ys => check_element_rec x i (augment _ ys) ds
  end.

Theorem check_element_unsat_valid : forall (elem : element) (ds : domset),
    check_element_unsat elem ds = true -> cst_is_unsat ElemConstraint elem ds.
Proof.
  unfold cst_is_unsat, eval.
  unfold ElemConstraint, eval_element, check_element_unsat; destruct elem.
  generalize (augment _ l); intros l0 ds; induction l0.

  intros; unfold eval_element_rec in H1; contradiction.

  unfold check_element_rec, eval_element_rec, augment, augment_rec in *;
    fold augment_rec in *; fold check_element_rec in *; fold eval_element_rec in *.
  destruct a.
  rewrite andb_true_iff; rewrite orb_true_iff; rewrite negb_true_iff.
  intros.
  destruct H as [Hc Hr].

  destruct H1 as [Hz | Ht]; [destruct Hz as [Hz Hi] | apply IHl0 with (theta := theta) in Ht];
    try congruence.                                                                                        
  destruct Hc.
  + assert (Hd := term_dom_valid ds theta H0 i0).
    rewrite Hz in Hd.
    apply satb_dom_iff in Hd; congruence.
  + rewrite dom_unsatb_unsat in H.
    assert (sat_dom (dom_meet (term_dom ds i) (term_dom ds i1)) (eval_iterm i theta)).
    apply dom_meet_iff; split.
      apply (term_dom_valid ds theta H0 i).
      rewrite Hi; apply (term_dom_valid ds theta H0 i1).
    specialize (H (eval_iterm i theta)); contradiction.
Qed.

Definition ElemCheckUnsat := mkUnsatChecker ElemConstraint (check_element_unsat) (check_element_unsat_valid).

Fixpoint eval_element_sol_rec (x : iterm) (i : iterm) ys (theta : valuation) :=
  match ys with
  | nil => false
  | cons (k, y) ys' =>
    (Z.eqb (eval_iterm i theta)  k) && (Z.eqb (eval_iterm x theta) (eval_iterm y theta))
      || eval_element_sol_rec x i ys' theta
  end.

Definition eval_element_sol (con : element) (theta : valuation) :=
  match con with
  | Element x i ys => eval_element_sol_rec x i (augment _ ys) theta
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


(* Now add member/nonmember constraints *)
Inductive member : Type :=
| Mem : iterm -> list iterm -> member.

Ltac list_ext :=
  repeat (
  match goal with
    | [ |- context[List.Exists _ _] ] => rewrite List.Exists_exists
    | [ |- context[List.Forall _ _] ] => rewrite List.Forall_forall                                 
    | [ |- context[List.forallb _ _ = true] ] => rewrite List.forallb_forall
    | [ |- context[List.existsb _ _ = true] ] => rewrite List.existsb_exists
    | [ H : context[ List.Exists _ _ ] |- _ ] => rewrite List.Exists_exists in H
    | [ H : context[List.Forall _ _] |- _ ] => rewrite List.Forall_forall in H
    | [ H : context[List.forallb _ _ = true] |- _ ] => rewrite List.forallb_forall in H
    | [ H : context[List.existsb _ _ = true] |- _ ] => rewrite List.existsb_exists in H
  end).

Definition eval_member mem theta :=
  match mem with
      | Mem z xs => List.Exists (fun x => (eval_iterm z theta) = (eval_iterm x theta)) xs
  end.
Definition check_member_sol mem theta :=
  match mem with
    | Mem z xs =>
      let z' := eval_iterm z theta in
      List.existsb (fun x => Z.eqb z' (eval_iterm x theta)) xs
  end.
Lemma check_member_sol_valid : forall mem theta, check_member_sol mem theta = true -> eval_member mem theta.
Proof.
  intros mem theta; destruct mem as [z xs].
  unfold check_member_sol, eval_member.
  list_ext; tsimpl; elim H; clear H; intros x Hx; exists x.
  now rewrite Z.eqb_eq in Hx.
Qed.
Definition check_member_unsat mem ds :=
  match mem with
    | Mem z xs =>
      let z' := term_dom ds z in
      List.forallb (fun x => dom_unsatb (dom_meet z' (term_dom ds x))) xs
  end.
Lemma check_member_unsat_valid :
  forall mem ds, check_member_unsat mem ds = true -> forall theta, eval_domset ds theta -> ~ eval_member mem theta.
Proof.
  intros mem ds; unfold check_member_unsat, eval_member; destruct mem as [z xs].
  list_ext; dom_simpl.
  intros Hf theta Hds. intro Hex.
  list_ext; elim Hex; clear Hex; intros x Hex; destruct Hex as [Hin Hx].
  specialize (Hf x Hin).
  rewrite dom_unsatb_unsat in Hf; unfold dom_unsat in Hf; specialize (Hf (eval_iterm x theta)).
  rewrite dom_meet_iff in Hf.
  assert (sat_dom (term_dom ds z) (eval_iterm x theta) /\ sat_dom (term_dom ds x) (eval_iterm x theta)).
    split; [rewrite <- Hx; apply term_dom_valid | apply term_dom_valid]; assumption.
  contradiction.
Qed.

Inductive notmember : Type :=
  | Notmem : iterm -> list iterm -> notmember.

Definition eval_notmember nmem theta :=
  match nmem with
    | Notmem z xs => List.Forall (fun x => (eval_iterm z theta) <> (eval_iterm x theta)) xs
  end.
Definition check_notmem_sol nmem theta :=
  match nmem with
    | Notmem z xs =>
      let z' := eval_iterm z theta in
      List.forallb (fun x => negb (Z.eqb z' (eval_iterm x theta))) xs
  end.
Lemma check_notmem_sol_valid : forall nmem theta, check_notmem_sol nmem theta = true -> eval_notmember nmem theta.
Proof.
  intros nmem theta; destruct nmem as [z xs]; unfold check_notmem_sol, eval_notmember.
  list_ext.
  intros Hc x Hin; specialize (Hc x Hin).
  tsimpl.
  rewrite <- Z.eqb_eq in H; congruence.
Qed.

Fixpoint notmem_holes ds xs holes :=
  match xs with
    | nil => holes
    | cons x xs' =>
      match db_constant_value (range_of_dom (term_dom ds x)) with
        | None => notmem_holes ds xs' holes
        | Some k => notmem_holes ds xs' (zset.add holes k)
      end
  end.
Lemma notmem_holes_holes :
  forall ds theta, eval_domset ds theta ->
                   forall xs holes k, ~ zset.mem holes k -> List.Forall (fun x => eval_iterm x theta <> k) xs -> ~ zset.mem (notmem_holes ds xs holes) k.
Proof.
  intros ds theta Hds xs holes k Hnm Hf.
  generalize holes Hnm; clear Hnm holes.
  induction xs.
  + intros; trivial.
  + intros holes Hnm.
    unfold notmem_holes; fold notmem_holes.
    eqelim (db_constant_value (range_of_dom (term_dom ds a))).
    - assert (Ha := db_constant_value_2 (range_of_dom (term_dom ds a)) z H0).
      list_ext.
      assert (forall x, List.In x xs -> eval_iterm x theta <> k) as H'.
        intros x Hin; apply Hf; now apply List.in_cons.
      apply (IHxs H' (zset.add holes z)).
      intro Hmem; apply zset.mem_addk_if in Hmem.
      destruct Hmem as [Hmem | Hmem]; try contradiction.
      rewrite Hmem in *.
      specialize (Hf a (List.in_eq a xs)).
      specialize (Ha (eval_iterm a theta)).
      assert (k = eval_iterm a theta).
        apply Ha.
        assert (He := term_dom_valid ds theta Hds a).
        unfold sat_dom in He; unfold range_of_dom; destruct (term_dom ds a); intuition.
      congruence.
    -  apply IHxs; try assumption.
       inversion Hf; assumption.
Qed.

Definition notmem_unsat_rec ds z xs :=
  let (z_db, z_holes) := term_dom ds z in
  match z_db with
  | (Bounded l, Bounded u) => zset.zset_covers (notmem_holes ds xs z_holes) l u
  | _ => false
  end.

Definition check_notmem_unsat nmem ds :=
  match nmem with
      | Notmem z xs =>
        notmem_unsat_rec ds z xs
  end.
Lemma check_notmem_unsat_valid :
  forall nmem ds, check_notmem_unsat nmem ds = true ->
                  forall theta, eval_domset ds theta -> ~ eval_notmember nmem theta.
Proof.
  intros nmem ds; destruct nmem as [z xs].
  unfold check_notmem_unsat, notmem_unsat_rec, eval_notmember.
  eqelim (term_dom ds z).
  destruct d; destruct b, b0; try (intros; congruence).
  intros Hcov.
  rewrite zset.zset_covers_spec in Hcov.
  intros theta Hds.
  assert (Hhole := notmem_holes_holes ds theta Hds xs z0).
  list_ext. intro.
  assert (Hdom := term_dom_valid ds theta Hds z).
  specialize (Hhole (eval_iterm z theta)).
  specialize (Hcov (eval_iterm z theta)).
  unfold sat_dom in Hdom; rewrite H0 in Hdom; destruct Hdom as [Hb Hh]; simpl in Hb, Hh.
  unfold sat_dbound, sat_lb, sat_ub in Hb; simpl in Hb.
  rewrite <- List.Forall_forall in H.
  assert (~ zset.mem (notmem_holes ds xs z0) (eval_iterm z theta)) as Hnm.
    apply Hhole; try assumption.
    refine (List.Forall_impl _ _ H); intuition.
  specialize (Hcov Hb); contradiction.
Qed.

Definition MembConstraint : Constraint :=
  mkConstraint (member) (eval_member).
Definition MembSolCheck := mkSolChecker MembConstraint check_member_sol check_member_sol_valid.
Definition MembCheck := mkUnsatChecker MembConstraint check_member_unsat check_member_unsat_valid.

Definition NotmemConstraint : Constraint :=
  mkConstraint (notmember) (eval_notmember).
Definition NotmemSolCheck := mkSolChecker NotmemConstraint check_notmem_sol check_notmem_sol_valid.
Definition NotmemCheck := mkUnsatChecker NotmemConstraint check_notmem_unsat check_notmem_unsat_valid.