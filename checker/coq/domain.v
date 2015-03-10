Require Import Bool.
Require Import ZArith.
Require List.
Require Import prim.
Require Import bounds.
Require Import zset.
Require SetoidList.

(* Exact representation of a variable domain. *)

(* A bounded interval, and a set of gaps. *)
Definition dom : Type := (dbound * zset)%type.

Definition dom_unconstrained : dom := ((Unbounded, Unbounded), empty).
Definition dom_const (k : Z) : dom := ((Bounded k, Bounded k), empty).
Definition dom_neq (k : Z) : dom := ((Unbounded, Unbounded), add empty k).
Definition dom_le (k : Z) : dom := ((Unbounded, Bounded k), empty).
Definition dom_ge (k : Z) : dom := ((Bounded k, Unbounded), empty).
Definition dom_range (l : Z) (u : Z) : dom := ((Bounded l, Bounded u), empty).

Definition sat_dom (d : dom) (k : Z) :=
  sat_dbound (fst d) k /\ ~ mem (snd d) k.

Definition satb_dom (d : dom) (k : Z) :=
  satb_dbound (fst d) k && negb (memb (snd d) k).

Definition dom_equal (dx dy : dom) := forall k : Z,
  sat_dom dx k <-> sat_dom dy k.

Definition eval_dom (d : (ivar * dom)) (theta : asg) :=
  sat_dom (snd d) (eval_ivar (fst d) theta).

Fixpoint sat_doms (ds : list (ivar * dom)) (x : ivar) (k : Z) :=
  match ds with
  | nil => True
  | cons (x', d) ds' => (x <> x' \/ sat_dom d k) /\ sat_doms ds' x k
  end.

Theorem sat_doms_alt : forall (ds : list (ivar * dom)) (x : ivar) (k : Z),
  sat_doms ds x k <->
    (forall (d : dom), List.In (x, d) ds -> sat_dom d k).
Proof.
  intros; induction ds.
  unfold sat_doms, List.In.
  split; intros; tauto.

  destruct a; simpl; unfold sat_doms; fold sat_doms; split; intros.
  apply List.in_inv in H0; destruct H.
  rewrite IHds in H1.
  destruct H0.
    inversion H0; destruct H; congruence.
    now apply H1.
    
  split.
  assert (x <> i \/ x = i). tauto.
  destruct H0; try (left; assumption).
  right; apply H.
  left; now rewrite H0.

  rewrite IHds; intros.
  apply H; tauto.
Qed.

Fixpoint eval_doms (ds : list (ivar * dom)) (theta : asg) :=
  match ds with
  | nil => True
  | cons d ds' => (eval_dom d theta) /\ (eval_doms ds' theta)
  end.

Theorem eval_doms_alt : forall (ds : list (ivar * dom)) (theta : asg),
  eval_doms ds theta <->
    (forall (d : ivar * dom), List.In d ds -> eval_dom d theta).
Proof.
  intros.
    induction ds.
      unfold eval_doms, List.In.
        split; intros; tauto.

      unfold eval_doms; fold eval_doms.
      split; intros.
        apply List.in_inv in H0.
        destruct H0; [rewrite <- H0; tauto | now apply IHds].
        split; [apply H; apply List.in_eq | apply IHds].
        intros; apply H; now apply List.in_cons with (a := a).
Qed.
        
Theorem satb_dom_true_iff_dom : forall (d : dom) (k : Z),
  satb_dom d k = true <-> sat_dom d k.
Proof.
  unfold satb_dom; unfold sat_dom. intros.
  rewrite andb_true_iff.
  rewrite satb_dbound_iff_db.
  rewrite negb_true_iff.
  rewrite <- memb_iff_mem.
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

Definition dom_is_unconstrained (d : dom) := forall (k : Z),
  sat_dom d k.
Theorem dom_unconstrained_is_uncon : dom_is_unconstrained dom_unconstrained.
Proof.
  unfold dom_is_unconstrained, dom_unconstrained, sat_dom; simpl.
  unfold sat_dbound, sat_lb, sat_ub; simpl; intros.
  assert (~ mem empty k). apply notmem_empty. tauto.
Qed.
 
Theorem dom_const_not_uncon : forall (k : Z), ~ dom_is_unconstrained (dom_const k).
Proof.
  intros.
    assert (~dom_is_unconstrained (dom_const k) \/ dom_is_unconstrained (dom_const k)). tauto.
    destruct H. assumption.
    unfold dom_is_unconstrained in H.
    assert (~ sat_dom (dom_const k) (Zsucc k)).
      unfold sat_dom, sat_dbound, sat_lb, sat_ub, dom_const; simpl. omega.
    assert (sat_dom (dom_const k) (Zsucc k)). apply H. tauto.
Qed.

Theorem dom_neq_not_uncon : forall (k : Z), ~ dom_is_unconstrained (dom_neq k).
Proof.
  intros.
    assert (~dom_is_unconstrained (dom_neq k) \/ dom_is_unconstrained (dom_neq k)). tauto.
    destruct H. assumption.
    unfold dom_is_unconstrained in H.
    assert (~ sat_dom (dom_neq k) k).
      unfold sat_dom, sat_dbound, sat_lb, sat_ub, dom_const; simpl.
      assert (mem (add empty k) k). apply mem_k_addk.
      tauto.
    assert (sat_dom (dom_neq k) k). apply H. tauto.
Qed.

Theorem dom_le_not_uncon : forall (k : Z), ~ dom_is_unconstrained (dom_le k).
Proof.
  intros.
    assert (~dom_is_unconstrained (dom_le k) \/ dom_is_unconstrained (dom_le k)). tauto.
    destruct H. assumption.
    unfold dom_is_unconstrained in H.
    assert (~ sat_dom (dom_le k) (Zsucc k)).
      unfold sat_dom, sat_dbound, sat_lb, sat_ub, dom_const; simpl. omega.
    assert (sat_dom (dom_le k) (Zsucc k)). apply H. tauto.
Qed.

Theorem dom_ge_not_uncon : forall (k : Z), ~ dom_is_unconstrained (dom_ge k).
Proof.
  intros.
    assert (~dom_is_unconstrained (dom_ge k) \/ dom_is_unconstrained (dom_ge k)). tauto.
    destruct H. assumption.
    unfold dom_is_unconstrained in H.
    assert (~ sat_dom (dom_ge k) (Zpred k)).
      unfold sat_dom, sat_dbound, sat_lb, sat_ub, dom_const; simpl.
      assert (Zpred k < k). apply Zlt_pred. omega.
    assert (sat_dom (dom_ge k) (Zpred k)). apply H. tauto.
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
  repeat (rewrite <- memb_iff_mem).
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

Theorem dom_meet_uncon_iff : forall (dx dy : dom),
 dom_is_unconstrained (dom_meet dx dy)
   <-> dom_is_unconstrained dx /\ dom_is_unconstrained dy.
Proof.
  intros; unfold dom_is_unconstrained.
  split; intros.
  assert (forall k : Z, sat_dom dx k /\ sat_dom dy k).
    intros; apply dom_meet_iff; apply H.
    split; intros.
      apply H0. apply H0.
  destruct H.
    apply dom_meet_iff. split.
      apply H. apply H0.
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
    split. tauto. apply notmem_empty.
    split. tauto. apply notmem_empty.

  assert (ivar_eqb x i = true <-> x = i) as Hxiff. apply ivar_eqb_iff_eq.
  destruct ivar_eqb; simpl in *.
  assert (x = i) as Hxi. rewrite <- Hxiff; trivial.
  clear Hxiff.
  rewrite Hxi; split. omega. apply notmem_empty.
  split. tauto. apply notmem_empty.

  unfold dom_unconstrained; simpl; split. tauto. apply notmem_empty.
  simpl; split. tauto. apply notmem_empty.

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
        apply notmem_empty.
      split. tauto. apply notmem_empty.
    
  assert (ivar_eqb x i = true <-> x = i) as Hxiff. apply ivar_eqb_iff_eq.
  destruct ivar_eqb; simpl in *.
    assert (x = i) as Hxi. rewrite <- Hxiff; trivial.
    clear Hxiff.
    rewrite Hxi; split.
      tauto.
      unfold mem, add. rewrite ZSets.add_spec.
      assert (~ mem empty (eval_ivar i theta)). apply notmem_empty.
      unfold mem in H0.
      tauto.
      split.
        tauto. apply notmem_empty.
      simpl; split. tauto. apply notmem_empty.
      tauto.
Qed.

Theorem not_litvar_iff_uncon : forall (x : ivar) (l : lit),
  lit_ivar l <> (Some x) <-> dom_is_unconstrained (dom_from_lit x l).
Proof.
  intros; split.
  unfold lit_ivar, vprop_ivar, dom_from_lit; destruct l; destruct v; simpl; intros.
    assert (ivar_eqb x i = true <-> x = i) as Hiff. apply ivar_eqb_iff_eq. destruct ivar_eqb.
    assert (x = i) as Hxi. now apply Hiff. congruence. apply dom_unconstrained_is_uncon.

    assert (ivar_eqb x i = true <-> x = i) as Hiff. apply ivar_eqb_iff_eq. destruct ivar_eqb.
    assert (x = i) as Hxi. now apply Hiff. congruence. apply dom_unconstrained_is_uncon.
    apply dom_unconstrained_is_uncon. apply dom_unconstrained_is_uncon. 

    assert (ivar_eqb x i = true <-> x = i) as Hiff. apply ivar_eqb_iff_eq. destruct ivar_eqb.
    assert (x = i) as Hxi. now apply Hiff. congruence. apply dom_unconstrained_is_uncon.

    assert (ivar_eqb x i = true <-> x = i) as Hiff. apply ivar_eqb_iff_eq. destruct ivar_eqb.
    assert (x = i) as Hxi. now apply Hiff. congruence. apply dom_unconstrained_is_uncon.
    apply dom_unconstrained_is_uncon. apply dom_unconstrained_is_uncon.

  unfold dom_from_lit, lit_ivar, vprop_ivar;
      destruct l; destruct v; simpl; intros. 
    assert (ivar_eqb x i = true <-> x = i) as Hiff. apply ivar_eqb_iff_eq. destruct ivar_eqb.
      assert (~ dom_is_unconstrained (dom_le z)). apply dom_le_not_uncon; tauto. tauto.
    assert (x <> i). rewrite <- Hiff; apply diff_false_true; congruence. congruence.

    assert (ivar_eqb x i = true <-> x = i) as Hiff. apply ivar_eqb_iff_eq. destruct ivar_eqb.
    assert (~ dom_is_unconstrained (dom_const z)). apply dom_const_not_uncon; tauto. tauto.
    assert (x <> i). rewrite <- Hiff; apply diff_false_true; congruence. congruence.

    congruence. congruence.
      
    assert (ivar_eqb x i = true <-> x = i) as Hiff. apply ivar_eqb_iff_eq. destruct ivar_eqb.
    assert (~ dom_is_unconstrained (dom_ge (z+1))). apply dom_ge_not_uncon; tauto. tauto.
    assert (x <> i). rewrite <- Hiff; apply diff_false_true; congruence. congruence.

    assert (ivar_eqb x i = true <-> x = i) as Hiff. apply ivar_eqb_iff_eq. destruct ivar_eqb.
    assert (~ dom_is_unconstrained (dom_neq z)). apply dom_neq_not_uncon; tauto. tauto.
    assert (x <> i). rewrite <- Hiff; apply diff_false_true; congruence. congruence.
    congruence. congruence.
Qed.

Fixpoint dom_from_negclause (x : ivar) (cl : clause) :=
  match cl with
  | nil => dom_unconstrained
  | cons l ls =>
      dom_meet (dom_from_lit x (neglit l)) (dom_from_negclause x ls)
  end.

Theorem not_clausevar_iff_uncon : forall (x : ivar) (cl : clause),
  ~ is_clausevar cl x <-> dom_is_unconstrained (dom_from_negclause x cl).
Proof.
  intros x cl; induction cl; simpl.
    assert (dom_is_unconstrained dom_unconstrained). apply dom_unconstrained_is_uncon.
    tauto.

  split; intros.
    assert (lit_ivar a <> Some x /\ ~is_clausevar cl x). tauto.
    assert (dom_is_unconstrained (dom_from_lit x (neglit a))).
      apply not_litvar_iff_uncon. rewrite <- neglit_ivar. tauto.
    apply dom_meet_uncon_iff; split; simpl. assumption.
      apply IHcl; apply H0.

    apply dom_meet_uncon_iff in H. destruct H as [Hl Hcl].
    assert (lit_ivar a <> Some x).
      rewrite neglit_ivar; apply not_litvar_iff_uncon. assumption. tauto.
Qed.
        
Fixpoint negclause_of_holes x (ks : list Z) :=
  match ks with
  | nil => nil
  | cons k ks' =>
      cons (Pos (IEq x k)) (negclause_of_holes x ks')
  end.

Theorem sat_negclause_holes'_iff : forall (x x' : ivar) (ks : list Z) (k' : Z),
  sat_negclause (negclause_of_holes x ks) x' k' <->
    (x <> x' \/ ~ List.In k' ks).
Proof.
  intros; induction ks.
  unfold sat_negclause, negclause_of_holes, List.In; tauto.

  unfold negclause_of_holes; simpl; fold negclause_of_holes.
  rewrite IHks.
  assert (x <> x' \/ x = x'). tauto.
  destruct H; split; intros.
  left; assumption.
  split; left; congruence.
  destruct H0; right; intro.
  destruct H0, H1, H2; congruence.
  destruct H0; try congruence.
  repeat (rewrite H). 
  assert (a <> k' /\ ~ List.In k' ks). tauto.
  destruct H1.
  split; right; congruence.
Qed.
    
Theorem sat_negclause_holes_iff : forall (x x' : ivar) (ks : ZSets.t) (k : Z),
  (x <> x' \/ (~ mem ks k)) <->
    sat_negclause (negclause_of_holes x (ZSets.elements ks)) x' k.
Proof.
  intros.
  unfold mem.
  assert (sat_negclause (negclause_of_holes x (ZSets.elements ks)) x' k <-> (x <> x' \/ ~ List.In k (ZSets.elements ks))).
    apply sat_negclause_holes'_iff.
    rewrite H.
  assert (x <> x' \/ x = x'). tauto.
  destruct H0; split; intros; try (left; congruence).
  destruct H1; try congruence.
  right.
  intro.
  apply SetoidList.In_InA with (eqA := eq) in H2.
  now apply ZSets.elements_spec1 in H2.
  apply Z_as_OT.eq_equiv.

  destruct H1; try tauto.
  right; intro; apply ZSets.elements_spec1 in H2.
  now apply InA_eq_iff_In in H2.
Qed.
  
Theorem negclause_of_holes_valid :
  forall x ks theta,
    eval_clause (negclause_of_holes x ks) theta <-> List.In (eval_ivar x theta) ks.
Proof.
  intros; induction ks.
  unfold eval_clause, List.In; simpl; try tauto.
  unfold eval_clause, negclause_of_holes;
    fold eval_clause; fold negclause_of_holes; simpl.
  rewrite IHks.
  split; intros; destruct H; simpl; try symmetry in H; try tauto.
Qed.

Theorem negclause_of_holes_valid_2 :
  forall x ks theta,
    SetoidList.InA eq (eval_ivar x theta) ks -> eval_clause (negclause_of_holes x ks) theta.
Proof.
  intros; induction ks.
    now apply SetoidList.InA_nil in H.

    unfold eval_clause, negclause_of_holes;
      fold eval_clause; fold negclause_of_holes; simpl.
    apply SetoidList.InA_cons in H.
    destruct H.
    rewrite H; tauto.
    tauto.
Qed.

Theorem sat_dom_lit_iff : forall (l : lit) (x : ivar) (k : Z),
  sat_dom (dom_from_lit x l) k <-> sat_lit l x k.
Proof.
  intros.
    unfold sat_dom.
    unfold dom_from_lit, sat_lit.
    unfold dom_unconstrained, dom_le, dom_ge, dom_const, dom_neq, sat_dbound, sat_lb, sat_ub.
    destruct l; destruct v; simpl;
    try (remember (ivar_eqb x i) as exi; destruct exi); simpl;
      try (symmetry in Heqexi; rewrite ivar_eqb_iff_eq in Heqexi; rewrite <- Heqexi); split; intros.
    destruct H as [ [_ H] _]; now right.
    destruct H; [tauto | split].
    tauto. apply notmem_empty.
    left; intro; apply ivar_eqb_iff_eq in H0; congruence.
    split; [tauto | apply notmem_empty].
    destruct H; right; omega.
    split; [ destruct H ; [tauto | omega] | apply notmem_empty].
    left; intro; apply ivar_eqb_iff_eq in H0; congruence.
    split; [tauto | apply notmem_empty].
    trivial.
    split; [tauto | apply notmem_empty].
    trivial.
    split; [tauto | apply notmem_empty].
    destruct H; right; omega.
    split; [destruct H; [tauto | split ; [omega | tauto] ] | apply notmem_empty].
    left; intro; apply ivar_eqb_iff_eq in H0; congruence.
    split; [tauto | apply notmem_empty].
    destruct H; apply notmem_add_if in H0; destruct H0; right; congruence.
    split;
      [ tauto | intro; apply mem_addk_if in H0] .
    destruct H; [tauto | destruct H0 ; [ congruence | now apply notmem_empty in H0]].
    left; intro; apply ivar_eqb_iff_eq in H0; congruence.
    split ; [tauto | apply notmem_empty].
    trivial.
    split; [tauto | apply notmem_empty].
    trivial.
    split ; [tauto | apply notmem_empty].
Qed.
    
Definition negclause_of_dom (x : ivar) (d : dom) :=
  List.app (negclause_of_dbound x (fst d))
    (negclause_of_holes x (ZSets.elements (snd d))).

Theorem sat_negclause_dom_iff : forall (x x' : ivar) (d : dom) (k : Z),
  (x <> x' \/ sat_dom d k) <->
    sat_negclause (negclause_of_dom x d) x' k.
Proof.
  intros.
    unfold sat_dom, negclause_of_dom; destruct d; simpl.
    rewrite app_sat_negclause_and.
    rewrite <- sat_negclause_holes_iff, <- sat_negclause_db_iff.
    tauto.
Qed.

Theorem negclause_of_dom_valid : forall (x : ivar) (d : dom) (theta : asg),
  sat_dom d (eval_ivar x theta) <-> ~ eval_clause (negclause_of_dom x d) theta.
Proof.
  intros. unfold negclause_of_dom, sat_dom.
  rewrite notapp_clause_iff.
  rewrite negclause_of_dbound_valid.
  rewrite negclause_of_holes_valid with (ks := (ZSets.elements (snd d))).
  unfold mem.
  rewrite <- ZSets.elements_spec1.
  split; intros; split; intros; simpl; try tauto.
  intro; apply SetoidList.In_InA with (eqA := eq) in H0; try tauto.
  apply Z_as_OT.eq_equiv.

  destruct H. intro. apply negclause_of_holes_valid_2 in H1.
  rewrite negclause_of_holes_valid in H1.
  tauto.
Qed.

Fixpoint negclause_of_doms (ds : list (ivar * dom)) :=
  match ds with
  | nil => nil
  | cons (x, d) ds' => 
      List.app (negclause_of_dom x d) (negclause_of_doms ds')
  end.
Theorem sat_negclause_doms_iff : forall (ds : list (ivar * dom)) (x : ivar) (k : Z),
  sat_doms ds x k <-> sat_negclause (negclause_of_doms ds) x k.
Proof.
  intros.
  induction ds.
    now unfold sat_doms, negclause_of_doms, sat_negclause.

    unfold sat_doms, negclause_of_doms; simpl; fold sat_doms; fold negclause_of_doms.
    destruct a; simpl.
    rewrite app_sat_negclause_and.
    rewrite <- IHds.
    rewrite <- sat_negclause_dom_iff.
    split; intros; destruct H; split; try tauto; try (destruct H; [left; congruence | right; tauto]).
Qed.

Theorem negclause_of_doms_valid : forall (ds : list (ivar * dom)) (theta : asg),
  eval_doms ds theta <-> ~ eval_clause (negclause_of_doms ds) theta.
Proof.
  intros; induction ds; unfold eval_doms, negclause_of_doms; simpl; try tauto.

  fold eval_doms; fold negclause_of_doms; destruct a; simpl.
  rewrite notapp_clause_iff.
  rewrite IHds; rewrite <- negclause_of_dom_valid; unfold eval_dom; simpl; tauto.
Qed.
  
Fixpoint db_of_doms (x : ivar) (ds : list (ivar * dom)) :=
  match ds with
  | nil => (Unbounded, Unbounded)
  | cons (y, d) ds' =>
      if ivar_eqb x y then
        db_meet (fst d) (db_of_doms x ds') 
      else
        db_of_doms x ds'
  end.

Theorem sat_dom_negclause_iff : forall (cl : clause) (x : ivar) (k : Z),
  sat_dom (dom_from_negclause x cl) k <-> sat_negclause cl x k.
Proof.
  intros.
  induction cl; unfold dom_from_negclause, sat_negclause; simpl.
  assert (H := dom_unconstrained_is_uncon); unfold dom_is_unconstrained in H.
  assert (H' := H k); tauto.

  fold dom_from_negclause; fold sat_negclause.
  rewrite dom_meet_iff.
  rewrite IHcl.
  apply and_iff_compat_r.
  apply sat_dom_lit_iff.
Qed.

Theorem dom_from_negclause_valid : forall (x : ivar) (cl : clause) (theta : asg),
 ~eval_clause cl theta -> sat_dom (dom_from_negclause x cl) (eval_ivar x theta).
Proof.
  intros.
  induction cl.
  unfold dom_from_negclause, dom_unconstrained;
  unfold sat_dom, sat_dbound; simpl. split. tauto. apply notmem_empty.

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

Definition dom_unsatb (d : dom) :=
  match d with
  | (db, holes) =>
    match (fst db) with
    | Unbounded => false
    | Bounded lb =>
      match (snd db) with
      | Unbounded => false
      | Bounded ub =>
        zset_covers holes lb ub
      end
    end
  end.
Theorem dom_unsatb_unsat : forall (d : dom),
  dom_unsatb d = true <-> forall (k : Z), ~ sat_dom d k.
Proof.
  unfold dom_unsatb; intros; destruct d as (db, z); destruct db as (l, u); simpl.

  destruct l, u; simpl.

  split.
    discriminate. intros Hun.
    assert (~ sat_dom (Unbounded, Unbounded, z) (Zpred (zset_min_lb z 0))).
      apply Hun.
    rewrite <- satb_dom_false_iff_notdom in H.
    unfold satb_dom in H. simpl in H.
    
    apply negb_false_iff in H.
    rewrite memb_iff_mem in H.
    apply lt_min_notin_zset with (k := 0) in H. tauto.
    apply Zlt_pred.

  split.
    discriminate. intros Hun.
    assert (~ sat_dom (Unbounded, Bounded z0, z) (Zpred (zset_min_lb z z0))).
      apply Hun.
    rewrite <- satb_dom_false_iff_notdom in H.
    unfold satb_dom in H; apply andb_false_iff in H; simpl in H.
    destruct H.
      unfold satb_dbound, satb_lb, satb_ub in H; simpl in H.
      apply Z_leb_false_iff_notle in H.
      assert (zset_min_lb z z0 <= z0).
        apply zset_min_lb_le.
      assert False.
      assert (Zpred (zset_min_lb z z0) < zset_min_lb z z0).
        apply Zlt_pred.
      omega. tauto.

    apply negb_false_iff in H.
    rewrite memb_iff_mem in H.
    apply lt_min_notin_zset with (k := z0) in H. tauto.
    apply Zlt_pred.

  split.
    discriminate. intros Hun.
    assert (~ sat_dom (Bounded z0, Unbounded, z) (Zsucc (zset_max_ub z z0))).
      apply Hun.
    rewrite <- satb_dom_false_iff_notdom in H.
    unfold satb_dom in H; apply andb_false_iff in H; simpl in H.
    destruct H.
      unfold satb_dbound, satb_lb, satb_ub in H; simpl in H.
      rewrite andb_false_iff in H; simpl in H.
      destruct H.
      apply Z_leb_false_iff_notle in H.
      assert (z0 <= zset_max_ub z z0).
        apply zset_max_ub_lb.
      assert False.
      assert (zset_max_ub z z0 < Zsucc (zset_max_ub z z0)).
        apply Zlt_succ.
      omega. tauto. discriminate.

    apply negb_false_iff in H.
    rewrite memb_iff_mem in H.
    apply max_lt_notin_zset with (k := z0) in H. tauto.
    apply Zlt_succ.

    split.
      intros; apply satb_dom_false_iff_notdom.
      unfold satb_dom; apply andb_false_iff.
      assert (k < z0 \/ z1 < k \/ (z0 <= k <= z1)).
        omega.
      simpl.
      destruct H0.
        left. unfold satb_dbound, satb_lb, satb_ub; simpl.
        rewrite andb_false_iff; left.
        rewrite Z_leb_false_iff_notle. omega.

        destruct H0.
          left. unfold satb_dbound, satb_lb, satb_ub; simpl.
          rewrite andb_false_iff; right.
          rewrite Z_leb_false_iff_notle. omega.
          
        right. apply negb_false_iff; apply memb_iff_mem.
        rewrite zset_covers_spec in H; apply H. omega.
    
    intros; apply zset_covers_spec; intros.
    assert (~ sat_dom (Bounded z0, Bounded z1, z) k) as Hnd.
      apply H.
    apply satb_dom_false_iff_notdom in Hnd.
    unfold satb_dom in Hnd; apply andb_false_iff in Hnd.
    destruct Hnd as [Hnd | Hnd].
      unfold satb_dbound, satb_lb, satb_ub in Hnd; simpl in Hnd.
      apply andb_false_iff in Hnd.
      repeat (rewrite Z_leb_false_iff_notle in Hnd).
      assert False. omega. tauto.

      rewrite negb_false_iff in Hnd; simpl in Hnd.
      rewrite memb_iff_mem in Hnd; assumption.
Qed.

Theorem dom_from_lit_db : forall (l : lit) (x : ivar),
  fst (dom_from_lit x l) = db_from_lit x l.
Proof.
  intros; unfold dom_from_lit, db_from_lit, dom_unconstrained, dom_ge, dom_le, dom_neq;
    destruct l; destruct v;
      try (remember (ivar_eqb x i) as xi; destruct xi; symmetry in Heqxi; try rewrite ivar_eqb_iff_eq in Heqxi); simpl;
        try congruence.
Qed.

Theorem dom_from_negclause_db : forall (cl : clause) (x : ivar),
  fst (dom_from_negclause x cl) = db_from_negclause x cl.
Proof.
  intros; induction cl; intros.

  unfold dom_unconstrained; trivial.

  unfold db_from_negclause; fold db_from_negclause.
  unfold dom_from_negclause; fold dom_from_negclause.
  repeat (rewrite dom_from_lit_db); simpl.
  rewrite IHcl.
  now rewrite dom_from_lit_db.
Qed.

Theorem dom_meet_db : forall (dx dy : dom) (x y : dbound),
  fst dx = x /\ fst dy = y -> fst (dom_meet dx dy) = db_meet x y.
Proof.
  intros; unfold dom_meet; simpl.
  destruct H; now rewrite <- H, <- H0.
Qed.
(*
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
*)
Definition eval_tauto (tt : unit) (theta : asg) := True.

Definition check_tauto_var (cl : clause) (v : ivar) :=
  dom_unsatb (dom_from_negclause v cl).
Theorem check_tauto_var_valid : forall (cl : clause) (v : ivar) (theta : asg),
  check_tauto_var cl v = true -> eval_clause cl theta.
Proof.
  unfold check_tauto_var.
  intros cl v theta.
  assert (eval_clause cl theta \/ ~ eval_clause cl theta) as Hcl.
    tauto.
  destruct Hcl as [Hcl | Hncl].
    intros; assumption.
  apply dom_from_negclause_valid with (x := v) (cl := cl) in Hncl.
  intros.
  rewrite dom_unsatb_unsat in H.
  apply H in Hncl. tauto.
Qed.
    
Definition check_tauto_vprop (cl : clause) (vp : vprop) :=
  match vp with
  | ILeq x k => check_tauto_var cl x
  | IEq x k => check_tauto_var cl x
  | _ => false
  end.

Theorem check_tauto_vprop_valid : forall (cl : clause) (vp : vprop) (theta : asg),
  check_tauto_vprop cl vp = true -> eval_clause cl theta.
Proof.
  unfold check_tauto_vprop; intros; destruct vp.
  apply check_tauto_var_valid with (v := i); assumption.
  apply check_tauto_var_valid with (v := i); assumption.
  discriminate.
  discriminate.
Qed.

Definition check_tauto_lit (cl : clause) (l : lit) :=
  match l with
  | Pos vp =>
    match vp with
    | CTrue => true
    | _ => check_tauto_vprop cl vp
    end
  | Neg vp => check_tauto_vprop cl vp
  end.
Theorem check_tauto_lit_valid : forall (cl : clause) (l : lit) (theta : asg),
  (eval_lit l theta -> eval_clause cl theta) ->
    check_tauto_lit cl l = true -> eval_clause cl theta.
Proof.
  unfold check_tauto_lit; intros; destruct l. destruct v.

  apply check_tauto_vprop_valid with (vp := (ILeq i z)) (theta := theta); assumption.
  apply check_tauto_vprop_valid with (vp := (IEq i z)) (theta := theta); assumption.
  apply check_tauto_vprop_valid with (vp := (BTrue b)) (theta := theta); assumption.
  unfold eval_lit in H; unfold eval_vprop in H.
  apply H; trivial.

  apply check_tauto_vprop_valid with (vp := v); assumption.
Qed.

Fixpoint check_tauto_rec (cl : clause) (ls : list lit) :=
  match ls with
  | nil => false
  | cons l ls' => check_tauto_lit cl l || check_tauto_rec cl ls'
  end.

Theorem check_tauto_rec_valid : forall (cl : clause) (ls : clause) (theta : asg),
  (eval_clause ls theta -> eval_clause cl theta) ->
    check_tauto_rec cl ls = true -> eval_tauto tt theta -> eval_clause cl theta.
Proof.
  unfold implies, eval_tauto.
  intros cl ls theta; induction ls.
    unfold check_tauto_rec; intros; discriminate.

    unfold check_tauto_rec; fold check_tauto_rec.
    rewrite orb_true_iff.
    intros.
    destruct H0 as [Ha | Hcl].
    unfold eval_clause in H; fold eval_clause in H.
      apply check_tauto_lit_valid with (theta := theta) in Ha.
      assumption.

      intro; apply H; left; assumption.
      
      unfold eval_clause in H; fold eval_clause in H.
      tauto.
Qed.

Definition check_tauto (tt : unit) (cl : clause) := check_tauto_rec cl cl.
Theorem check_tauto_valid : forall (tt : unit) (cl : clause),
  check_tauto tt cl = true -> implies (eval_tauto tt) (eval_clause cl).
Proof.
  unfold check_tauto; intros.
  unfold implies; intro theta.
  assert (eval_clause cl theta -> eval_clause cl theta). tauto.
  apply check_tauto_rec_valid with (cl := cl) (ls := cl); assumption.
Qed.

Definition Tauto : Constraint :=
  mkConstraint (unit) (eval_tauto).
Definition CheckTauto := mkChecker Tauto (check_tauto) (check_tauto_valid).

Definition BoundedTauto := BoundedConstraint Tauto.
Definition BoundedTautoChk := BoundedChecker Tauto CheckTauto.
Definition check_tauto_bnd (bnd : list (ivar*Z*Z)) (cl : clause) :=
  check BoundedTauto BoundedTautoChk (bnd, tt) cl.

Definition domfun := ivar -> dom.
Definition dbfun := ivar -> dbound.
Definition eval_domfun (f : domfun) (theta : asg) :=
  forall x : ivar, sat_dom (f x) (eval_ivar x theta).

Definition eval_dbfun (f : dbfun) (theta : asg) :=
  forall x : ivar, sat_dbound (f x) (eval_ivar x theta).

Definition domfun_meet (f g : domfun) (x : ivar) :=
  dom_meet (f x) (g x).

Theorem domfun_meet_iff :
  forall (f g : domfun) (x : ivar) (k : Z),
    sat_dom ((domfun_meet f g) x) k <->
      sat_dom (f x) k /\ sat_dom (g x) k.
Proof.
  intros; unfold domfun_meet.
  now rewrite dom_meet_iff.
Qed.

Definition dbfun_meet (f g : dbfun) (x : ivar) :=
  db_meet (f x) (g x).

Definition is_negcl_domfun (f : domfun) (cl : clause) :=
  forall (x : ivar) (k : Z),
    sat_dom (f x) k <-> sat_dom (dom_from_negclause x cl) k.
  
Theorem negcl_domfun_valid : forall x f cl,
  is_negcl_domfun f cl ->
    forall theta, ~ eval_clause cl theta -> sat_dom (f x) (eval_ivar x theta).
Proof.
  unfold is_negcl_domfun, dom_equal; intros.
  rewrite H; now apply dom_from_negclause_valid.
Qed.

Definition is_negcl_domfun_db (f : domfun) (cl : clause) :=
  forall (x : ivar),
    (fst (f x)) = db_from_negclause x cl.
Definition is_negcl_dbfun (f : dbfun) (cl : clause) :=
  forall (x : ivar),
    f x = db_from_negclause x cl.

(*
Theorem bounded_negcl_domfun_valid : forall x f g cl theta,
  eval_domfun f theta /\ is_negcl_domfun g cl ->
    ~ eval_clause cl theta -> sat_dom ((domfun_meet f g) x) (eval_ivar x theta).
Proof.
  intros.
    destruct H ; apply domfun_meet_iff; split.
      apply H.
      now apply negcl_domfun_valid with (cl := cl).
Qed.
*)

Theorem app_dom_from_negclause_iff : forall c d x k,
  sat_dom (dom_from_negclause x (List.app c d)) k <->
    sat_dom (dom_from_negclause x c) k /\ sat_dom (dom_from_negclause x d) k.
Proof.
  intros.
  induction c.
  unfold dom_from_negclause at 1; simpl; fold dom_from_negclause.
  assert (sat_dom dom_unconstrained k).
    apply dom_unconstrained_is_uncon.
  tauto.

  unfold dom_from_negclause; simpl; fold dom_from_negclause.
  repeat (rewrite dom_meet_iff).
  tauto.
Qed.

Theorem app_dom_from_negclause_db_eq : forall c d x,
  fst (dom_from_negclause x (List.app c d)) =
    fst (dom_meet (dom_from_negclause x c) (dom_from_negclause x d)).
Proof.
  intros.
  induction c.
  unfold dom_from_negclause at 1; simpl; fold dom_from_negclause.
  unfold db_meet; simpl.
  now rewrite <- surjective_pairing.

  unfold dom_from_negclause; simpl; fold dom_from_negclause.
  rewrite IHc.
  remember (fst (dom_from_lit x (neglit a))) as g.
  remember (fst (dom_from_negclause x c)) as h.
  remember (fst (dom_from_negclause x d)) as i.
  rewrite dom_meet_db with (x := h) (y := i).
  now rewrite <- db_meet_assoc.
  rewrite <- Heqi, <- Heqh. tauto.
Qed.

Theorem app_negcl_domfun_if : forall c d f g,
  is_negcl_domfun f c /\ is_negcl_domfun g d -> is_negcl_domfun (domfun_meet f g) (List.app c d).
Proof.
  unfold is_negcl_domfun; intros.
  rewrite app_dom_from_negclause_iff.
  destruct H.
  rewrite <- H, <- H0.
  apply domfun_meet_iff.
Qed.

Theorem app_negcl_domfun_db_if : forall c d f g,
  is_negcl_domfun_db f c /\ is_negcl_domfun_db g d -> is_negcl_domfun_db (domfun_meet f g) (List.app c d).
Proof.
  unfold is_negcl_domfun_db; intros.
  unfold domfun_meet.
  rewrite dom_meet_db with (x := (fst (f x))) (y := (fst (g x))).
  destruct H.
  rewrite H, H0.
  repeat (rewrite <- dom_from_negclause_db).
  rewrite app_dom_from_negclause_db_eq.
  now rewrite dom_meet_db with (x := fst (dom_from_negclause x c)) (y := fst (dom_from_negclause x d)).
  tauto.
Qed.

Theorem app_negcl_dbfun_if : forall c d f g,
  is_negcl_dbfun f c /\ is_negcl_dbfun g d -> is_negcl_dbfun (dbfun_meet f g) (List.app c d).
Proof.
  unfold is_negcl_dbfun; intros.
  unfold dbfun_meet.
  rewrite app_db_from_negclause_meet.
  destruct H.
  now rewrite H, H0.
Qed.

Record DomCheck (C : Constraint) : Type := mkDomCheck
  {
    dc_check : C.(T) -> domfun -> bool ;
    dc_check_valid : 
      forall (x : C.(T)) (f : domfun) (cl : clause),
      is_negcl_domfun f cl /\ dc_check x f = true ->
        implies (C.(eval) x) (eval_clause cl) }.

Record DomDBCheck (C : Constraint) : Type := mkDomDBCheck
  { db_check : C.(T) -> dbfun -> bool ;
    db_check_valid : 
      forall (x : C.(T)) (f : dbfun) (cl : clause),
      is_negcl_dbfun f cl /\ db_check x f = true ->
        implies (C.(eval) x) (eval_clause cl) }.

(*
Theorem dombounded_negcl_iff :
  forall (f g : domfun) (cl : clause) (theta : asg),
  eval_domfun f theta ->
    (eval_domfun g theta -> eval_clause cl theta) ->
    (eval_domfun (domfun_meet f g) theta -> eval_clause cl theta).
Proof.
  intros.
  unfold eval_domfun in H1.
  apply H0; unfold eval_domfun; intros.
  now apply domfun_meet_iff with (f := f).
Qed.
     
Definition dombounded (C : DomCheck) : Type :=
  (domfun * C.(T))%type.
Definition dombounded_eval (C : DomCheck) (x : dombounded C) (theta : asg) :=
  eval_domfun (fst x) theta /\ C.(eval) (snd x) theta.
Definition dombounded_check (C : DomCheck) (x : dombounded C) (f : domfun) :=
  C.(check) (snd x) (domfun_meet f (fst x)).
Theorem dombounded_check_valid : forall (C : DomCheck) (x : dombounded C) (f : domfun) (cl : clause),
  is_negcl_domfun f cl /\ dombounded_check C x f = true -> implies (dombounded_eval C x) (eval_clause cl).
Proof.
  intros.
    destruct H.
    unfold dombounded_eval.
    unfold implies; intros.
    
    assert (is_negcl_domfun f cl /\ C.(check) (snd x) f = true ->
      implies (C.(eval) (snd x)) (eval_clause cl)) as Cvalid.
      intros. apply C.(check_valid) with (f := f).
      tauto.
    destruct H1.
    unfold implies in Cvalid.
    apply Cvalid.
    split.
      assumption.
      
    apply C.(check_valid).
    apply dombounded_negcl_iff with (f := f) (g := (fst x)).
    unfold implies, dombounded_eval; intros.
    destruct H1.
      intros; apply C.(check_valid) with (f := f); split; assumption.
    unfold is_negcl_domfun in H.
    unfold dombounded_eval, implies; intros.
    destruct H2.
    Check C.(check_valid).
    unfold dombounded_eval.
    apply C.(check_valid).
    destruct H0.
    apply C.(check_valid).
    unfold implies in H.
    assert (eval_clause (negclause_of_bounds (fst x) ++ cl) theta).
      apply H. exact H1.
    apply app_clause_or in H2.
    rewrite negclause_of_bounds_valid in H0.
    destruct H2.
      tauto.
      exact H2.
Qed.
*)

Theorem eval_domfun_meet_iff : forall (f g : domfun) (theta : asg),
  eval_domfun (fun x => dom_meet (f x) (g x)) theta <-> eval_domfun f theta /\ eval_domfun g theta.
Proof.
  unfold eval_domfun; intros; split; intros.
  split; intros;
    [apply dom_meet_iff with (dy := g x) | apply dom_meet_iff with (dx := f x)]; apply H.
  destruct H as [Hf Hg]; rewrite dom_meet_iff; split; [apply Hf | apply Hg].
Qed.

Lemma zle_ind : forall (z z' : Z),
  ((forall k, (True /\ k <= z <-> True /\ k <= z')) <-> z = z').
Proof.
  intros; split; intros.
  assert (z = z' \/ z < z' \/ z > z').
    omega.
  destruct H0; try assumption.
  assert (z <= z); assert (z' <= z'); try omega.
  destruct H0; assert False.
    assert (H' := H z'). assert (z' <= z). tauto.
    omega. contradiction.
    assert (H' := H z); assert (z <= z'). tauto. omega. contradiction.
  now rewrite H.
Qed.

Theorem lb_equal_alt : forall (b b' : bound),
  b = b' <-> forall k, sat_lb b k <-> sat_lb b' k.
Proof.
  split; unfold sat_lb; intros.
    now rewrite H.
    destruct b, b'; try congruence.
    assert (z <= (z-1)). apply H; tauto.
    assert False. omega. contradiction.

    assert (z <= (z-1)). apply H; tauto.
    assert False. omega. contradiction.
    assert (z = z0 \/ z < z0 \/ z0 < z).
      omega.
    destruct H0; [now rewrite H0 | destruct H0].
    assert (z0 <= z). apply H; omega. assert False. omega. contradiction.
    assert (z <= z0). apply H; omega. assert False. omega. contradiction.
Qed.

Theorem ub_equal_alt : forall (b b' : bound),
  b = b' <-> forall k, sat_ub b k <-> sat_ub b' k.
Proof.
  split; unfold sat_ub; intros.
    now rewrite H.
    destruct b, b'; try congruence.
    assert ((z+1) <= z). apply H; tauto.
    assert False. omega. contradiction.

    assert ((z+1) <= z). apply H; tauto.
    assert False. omega. contradiction.
    assert (z = z0 \/ z < z0 \/ z0 < z).
      omega.
    destruct H0; [now rewrite H0 | destruct H0].
    assert (z0 <= z). apply H; omega. assert False. omega. contradiction.
    assert (z <= z0). apply H; omega. assert False. omega. contradiction.
Qed.

Theorem forall_split : forall (A : Type) P Q,
  (forall x : A, P x <-> Q x) <-> (forall x : A, P x -> Q x) /\ (forall x : A, Q x -> P x).
Proof.
  intros; split; intros.
  split ; [apply H | apply H].
  destruct H. split; intros; [now apply H | now apply H0].
Qed.

Theorem forall_and : forall (A : Type) P Q,
  (forall x : A, P x /\ Q x) <-> (forall x : A, P x) /\ (forall x : A, Q x).
Proof.
  intros; split; intros.
  split; intros; assert (H' := H x); destruct H' as [Hp Hq]; assumption.
  destruct H as [Hp Hq]. split; [now apply Hp | now apply Hq].
Qed.

Theorem negclause_of_holes_db_uncon : forall (x x' : ivar) (zs : list Z),
  db_from_negclause x' (negclause_of_holes x zs) = (Unbounded, Unbounded).
Proof.
  intros.
    induction zs.
    now unfold negclause_of_holes, db_from_negclause.

    unfold db_from_negclause, negclause_of_holes; simpl.
    fold db_from_negclause; fold negclause_of_holes.
    rewrite IHzs.
    unfold db_meet; now simpl.
Qed.

Theorem app_db_from_negclause_iff : forall (cx cy : clause) (x : ivar),
  db_from_negclause x (List.app cx cy) = db_meet (db_from_negclause x cx) (db_from_negclause x cy).
Proof.
  intros; induction cx; intros.
  unfold db_from_negclause at 1 2; simpl; fold db_from_negclause.
  unfold db_meet; simpl.
  now rewrite <- surjective_pairing.

  unfold db_from_negclause; simpl; fold db_from_negclause.
  rewrite IHcx; now rewrite db_meet_assoc.
Qed.

Theorem negclause_of_lb_inv : forall (b : bound) (x : ivar),
  db_from_negclause x (negclause_of_lb x b) = (b, Unbounded).
Proof.
  intros.
    unfold db_from_negclause, negclause_of_lb; destruct b; simpl; try congruence.
    assert (ivar_eqb x x = true). now apply ivar_eqb_iff_eq.
    remember (ivar_eqb x x) as xx; destruct xx.
    unfold db_meet; simpl.
    apply injective_projections; simpl.
    apply f_equal; omega. trivial. discriminate.
Qed.

Theorem negclause_of_ub_inv : forall (b : bound) (x : ivar),
  db_from_negclause x (negclause_of_ub x b) = (Unbounded, b).
Proof.
  intros.
    unfold db_from_negclause, negclause_of_ub; destruct b; simpl; try congruence.
    assert (ivar_eqb x x = true). now apply ivar_eqb_iff_eq.
    remember (ivar_eqb x x) as xx; destruct xx.
    unfold db_meet; simpl.
    apply injective_projections; simpl.
    trivial. trivial. discriminate.
Qed.

Theorem negclause_of_db_inv : forall (db : dbound) (x : ivar),
  db_from_negclause x (negclause_of_dbound x db) = db.
Proof.
  intros.
    unfold db_from_negclause, negclause_of_dbound.
    fold db_from_negclause.
    rewrite app_db_from_negclause_iff.
    rewrite negclause_of_lb_inv.
    rewrite negclause_of_ub_inv.
    unfold db_meet, bound_max; simpl.
    destruct db; destruct b; simpl; trivial.
Qed.

Theorem negclause_of_dom_db_inv : forall (d : dom) (x x' : ivar),
  x = x' -> db_from_negclause x' (negclause_of_dom x d) = fst d.
Proof.
  intros.
  destruct d; simpl.
  rewrite <- H.
  rewrite <- dom_from_negclause_db; destruct d; simpl.
  unfold negclause_of_dom, dom_from_negclause. simpl.
  fold dom_from_negclause.
  rewrite app_dom_from_negclause_db_eq.
  remember (dom_from_negclause x (negclause_of_dbound x (b, b0))) as dcl.
  remember (dom_from_negclause x (negclause_of_holes x (ZSets.elements z))).
  rewrite dom_meet_db with (x := fst dcl) (y := fst d); try (split; trivial).
  rewrite Heqdcl, Heqd.
  repeat (rewrite dom_from_negclause_db).
  rewrite negclause_of_db_inv.
  rewrite negclause_of_holes_db_uncon.
  unfold db_meet; simpl.
  unfold bound_max, bound_min; destruct b, b0; simpl; try congruence.
Qed.

Theorem negclause_of_dom_db_inv2 : forall (x x' : ivar) (d : dom),
  x <> x' -> db_from_negclause x' (negclause_of_dom x d) = (Unbounded, Unbounded).
Proof.
  intros.
    unfold negclause_of_dom.
    rewrite app_db_from_negclause_meet.
    rewrite negclause_of_holes_db_uncon.
    assert (ivar_eqb x' x = false).
      apply not_true_is_false; intro; apply ivar_eqb_iff_eq in H0; congruence.
    destruct d; destruct d;
      unfold db_meet, db_from_negclause, negclause_of_dbound, negclause_of_lb, negclause_of_ub;
      destruct b, b0; simpl; try destruct (ivar_eqb x' x);
        unfold bound_min, bound_max; simpl; try congruence.
Qed.
  
Theorem negclause_of_doms_db_eq : forall (x : ivar) (ds : list (ivar * dom)),
  db_from_negclause x (negclause_of_doms ds) = db_of_doms x ds.
Proof.
  intros; induction ds; intros; simpl; try trivial.

  destruct a; simpl.
  remember (ivar_eqb x i) as xi; symmetry in Heqxi; destruct xi.
  rewrite ivar_eqb_iff_eq in Heqxi; rewrite <- Heqxi.
  rewrite app_db_from_negclause_meet.
  rewrite IHds.
  now rewrite negclause_of_dom_db_inv.

  assert (x <> i). intro; apply ivar_eqb_iff_eq in H; congruence.
  rewrite app_db_from_negclause_meet.
  rewrite negclause_of_dom_db_inv2.
  rewrite IHds.
  unfold db_meet, bound_min, bound_max; simpl.
  now rewrite <- surjective_pairing.
  congruence.

Qed.

