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
  mkConstraint (unit) (eval_tauto) (check_tauto) (check_tauto_valid). 

Definition check_tauto_bnd (bnd : list (ivar*Z*Z)) (cl : clause) :=
  (BoundedConstraint Tauto).(check) (bnd, tt) cl.