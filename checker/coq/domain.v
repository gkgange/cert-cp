Require Import Bool.
Require Import ZArith.
Require List.
Require Import prim.
Require Import bounds.
Require Import zset.

(* Exact representation of a variable domain. *)

(* A bounded interval, and a set of gaps. *)
Definition dom : Type := (dbound * zset)%type.

Definition dom_unconstrained : dom := ((Unbounded, Unbounded), empty).
Definition dom_const (k : Z) : dom := ((Bounded k, Bounded k), empty).
Definition dom_neq (k : Z) : dom := ((Unbounded, Unbounded), add empty k).
Definition dom_le (k : Z) : dom := ((Unbounded, Bounded k), empty).
Definition dom_ge (k : Z) : dom := ((Bounded k, Unbounded), empty).

Definition sat_dom (d : dom) (k : Z) :=
  sat_dbound (fst d) k /\ ~ mem (snd d) k.

Definition satb_dom (d : dom) (k : Z) :=
  satb_dbound (fst d) k && negb (memb (snd d) k).

Theorem satb_dom_true_iff_dom : forall (d : dom) (k : Z),
  satb_dom d k = true <-> sat_dom d k.
Proof.
  unfold satb_dom; unfold sat_dom. intros.
  rewrite andb_true_iff.
  rewrite satb_dbound_iff_db.
  rewrite negb_true_iff.
  rewrite <- memb_true_iff_mem.
  split.
    intro; destruct H as [Hs Hm].
    rewrite Hm.
    split.
      exact Hs.
      apply diff_false_true.
    
    intro; destruct H as [Hs Hm].
    split.
      exact Hs.
      apply not_true_is_false; exact Hm.
Qed.

Theorem decidable_sat_dom : forall (db : dom) (k : Z),
  sat_dom db k \/ ~ sat_dom db k.
Proof.
  intros.
  rewrite <- satb_dom_true_iff_dom.
  tauto.
  Qed.

Theorem satb_dom_false_iff_notdom : forall (db : dom) (k : Z),
  satb_dom db k = false <-> ~ sat_dom db k.
Proof.
  intros.
  assert (sat_dom db k \/ ~sat_dom db k). apply decidable_sat_dom.
  destruct H.
  assert (satb_dom db k = true). apply satb_dom_true_iff_dom. exact H.
  rewrite H0.
  split. discriminate.
  intro. assert False. tauto. tauto.
 
  split.
  assert (sat_dom db k -> satb_dom db k = true). apply satb_dom_true_iff_dom.
  intro. tauto.
  
  intro.
  apply not_true_is_false.
  rewrite satb_dom_true_iff_dom. exact H.
Qed.

Definition dom_meet (dx dy : dom) :=
  (db_meet (fst dx) (fst dy), union (snd dx) (snd dy)).
Theorem dom_meet_iff : forall (dx dy : dom) (k : Z),
  sat_dom (dom_meet dx dy) k <-> sat_dom dx k /\ sat_dom dy k.
Proof.
  unfold sat_dom, dom_meet; intros.
  destruct dx, dy; simpl.
  rewrite mem_union_iff.
  repeat (rewrite <- memb_true_iff_mem).
  split.
    intros; destruct H as [Hd Hm].
    apply db_satmeet in Hd.
    destruct Hd as [Hd Hd0].
    split.
      split. exact Hd. tauto.
      split. exact Hd0. tauto.
  
    intro; destruct H as [Hl Hr].
    destruct Hl as [Hd Hmd]; destruct Hr as [Hd0 Hmd0].
    split.
      apply db_sat_impl_meet. tauto. tauto.
Qed.

Definition dom_from_lit (x : ivar) (l : lit) :=
  match l with
  | Pos (IEq x' k) =>
     if ivar_eqb x x' then dom_const k else dom_unconstrained
  | Neg (IEq x' k) =>
     if ivar_eqb x x' then dom_neq k else dom_unconstrained
  | Pos (ILeq x' k) =>
     if ivar_eqb x x' then dom_le k else dom_unconstrained
  | Neg (ILeq x' k) =>
     if ivar_eqb x x' then dom_ge (k+1) else dom_unconstrained
  | _ => dom_unconstrained
  end.

Theorem dom_from_lit_valid : forall (x : ivar) (l : lit) (theta : asg),
  eval_lit l theta -> sat_dom (dom_from_lit x l) (eval_ivar x theta).
Proof.
  unfold eval_lit, eval_vprop, dom_from_lit, sat_dom, sat_dbound.
  unfold sat_lb, sat_ub. intros.
  destruct l. destruct v.

  unfold dom_le, dom_unconstrained.
  assert (ivar_eqb x i = true <-> x = i) as Hxiff. apply ivar_eqb_iff_eq.
  destruct ivar_eqb; simpl in *.
    assert (x = i) as Hxi. apply Hxiff; trivial.
    clear Hxiff.
    rewrite Hxi.
    tauto.
    tauto.

  assert (ivar_eqb x i = true <-> x = i) as Hxiff. apply ivar_eqb_iff_eq.
  destruct ivar_eqb; simpl in *.
  assert (x = i) as Hxi. rewrite <- Hxiff; trivial.
  clear Hxiff.
  rewrite Hxi; omega.
  tauto.

  unfold dom_unconstrained; simpl; tauto. simpl; tauto.

  unfold dom_ge, dom_unconstrained, dom_neq;
  destruct v.
  assert (ivar_eqb x i = true <-> x = i) as Hxiff. apply ivar_eqb_iff_eq.
  destruct ivar_eqb; simpl in *.
    assert (x = i) as Hxi. rewrite <- Hxiff; trivial.
    clear Hxiff.
    rewrite Hxi; split.
      split.
        omega.
        tauto.
      tauto.
    tauto.
    
  assert (ivar_eqb x i = true <-> x = i) as Hxiff. apply ivar_eqb_iff_eq.
  destruct ivar_eqb; simpl in *.
    assert (x = i) as Hxi. rewrite <- Hxiff; trivial.
    clear Hxiff.
    rewrite Hxi; split.
      tauto.
      omega.
    tauto.
  simpl; tauto. simpl; tauto.
Qed.

Fixpoint dom_from_negclause (x : ivar) (cl : clause) :=
  match cl with
  | nil => dom_unconstrained
  | cons l ls =>
      dom_meet (dom_from_lit x (neglit l)) (dom_from_negclause x ls)
  end.

(*
Theorem dom_from_lit_complete : forall (x : ivar) (l : lit) (k : Z),
  sat_dom (dom_from_lit x l) k ->
    exists theta : asg, eval_lit l theta /\ (eval_ivar x theta) = k.
Proof.
  intros x l k; unfold sat_dom, dom_from_lit.
  unfold dom_le, dom_unconstrained, dom_const, dom_ge, dom_neq.
  destruct l.
    destruct v; simpl.

      assert (beq_nat x i = true <-> x = i) as Hxiff. apply beq_nat_true_iff.
      destruct beq_nat; simpl in *.
        assert (x = i) as Hxi. rewrite <- Hxiff; trivial.
        clear Hxiff.
        unfold sat_dbound; simpl.
        intro Hcond; destruct Hcond as [ [_ Hkz] _ ].
        rewrite Hxi.
      destruct beq_nat.
Qed.
*)  

Theorem dom_from_negclause_valid : forall (x : ivar) (cl : clause) (theta : asg),
 ~eval_clause cl theta -> sat_dom (dom_from_negclause x cl) (eval_ivar x theta).
Proof.
  intros.
  induction cl.
  unfold dom_from_negclause, dom_unconstrained;
  unfold sat_dom, sat_dbound; simpl. tauto.

  unfold eval_clause in H; fold eval_clause in H.
  unfold dom_from_negclause; fold dom_from_negclause.
  assert (~(eval_lit a theta) /\ ~(eval_clause cl theta)).
  apply Decidable.not_or; exact H. destruct H0.
  assert (eval_lit (neglit a) theta).
  apply neglit_not_lit. exact H0.
  assert (sat_dom (dom_from_lit x (neglit a)) (eval_ivar x theta)).
  apply dom_from_lit_valid; exact H2.
  assert (sat_dom (dom_from_negclause x cl) (eval_ivar x theta)).
  apply IHcl; exact H1.
  apply dom_meet_iff. split. exact H3. exact H4.
Qed.

Theorem notdom_negclause_impl_clause : forall (x : ivar) (cl : clause) (theta : asg),
  ~ sat_dbound (db_from_negclause x cl) (eval_ivar x theta) -> eval_clause cl theta.
Proof.
  intros.
  assert (eval_clause cl theta \/ ~ eval_clause cl theta). apply dec_evalclause.
  destruct H0.
  
  exact H0.
  assert (sat_dbound (db_from_negclause x cl) (eval_ivar x theta)).
  apply db_from_negclause_valid. exact H0.
  tauto.
Qed.

Theorem notsat_ub_impl_notdb : forall (db : dbound) (k : Z),
  ~ sat_ub (snd db) k -> ~ sat_dbound db k.
Proof.
  unfold sat_dbound; destruct db; simpl; intros.
  tauto.
Qed.

Theorem notsat_lb_impl_notdb : forall (db : dbound) (k : Z),
  ~ sat_lb (fst db) k -> ~ sat_dbound db k.
Proof.
  unfold sat_dbound; destruct db; simpl; intros. tauto.
Qed.
