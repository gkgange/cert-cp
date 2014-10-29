(* Computing domains/bounds from the complement of a clause. *)
Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import FSets.FMapFacts.
Require Import zset.
Require Import map.
Require Import prim.
Require Import bounds.
Require Import domain.

Fixpoint clause_varset cl :=
  match cl with
  | nil => empty
  | cons l cl' =>
    match lit_ivar l with
    | None => clause_varset cl'
    | Some x => add (clause_varset cl') x
    end
  end.

Theorem in_varset_iff_invars : forall (cl : clause) (x : ivar),
  mem (clause_varset cl) x <-> is_clausevar cl x.
Proof.
  intros cl x; induction cl.
  unfold clause_varset, is_clausevar.
  assert (~ mem empty x).
    apply notmem_empty.
  tauto.

  unfold clause_varset, is_clausevar; fold clause_varset; fold is_clausevar.
  destruct lit_ivar.
  split; intros.
    apply mem_addk_if in H.
    rewrite <- IHcl.
    destruct H.
      rewrite H; tauto.
      tauto.
    destruct H.
      assert (i = x). congruence.
      rewrite H0.
      apply mem_k_addk.
      apply mem_mem_add; tauto.

      rewrite IHcl; split.
      intros; right; assumption.
      intros; destruct H.
        discriminate. assumption.
Qed.

(* Mapping of variable names to domains. *)
Definition domset : Type := zmap dom.

Definition var_dom (ds : domset) (x : ivar) :=
  match ZMaps.find x ds with
  | None => dom_unconstrained
  | Some dom => dom
  end.

Theorem not_invars_uncon : forall (cl : clause) (x : ivar),
  ~ mem (clause_varset cl) x <-> dom_is_unconstrained (dom_from_negclause x cl).
Proof.
  intros.
  rewrite <- not_clausevar_iff_uncon.
  assert (mem (clause_varset cl) x <-> is_clausevar cl x).
    apply in_varset_iff_invars.
  tauto.
Qed.

Fixpoint negcl_domset' (cl : clause) (xs : list ivar) :=
  match xs with
  | nil => ZMaps.empty dom
  | cons x xs' => ZMaps.add x (dom_from_negclause x cl) (negcl_domset' cl xs')
  end.

(* Grabbed from a newer version of coq. *)
Lemma eq_option_alt : forall (elt : Type) (o o' : option elt),
  o = o' <-> (forall e, o=Some e <-> o' = Some e).
Proof.
  split; intros.
  subst; split; auto.
  destruct o; destruct o'; try rewrite H; auto.
  symmetry; rewrite <- H; auto.
Qed.

Lemma find_mapsto_iff : forall (A : Type) (m :ZMaps.t A) x e, ZMaps.MapsTo x e m <-> ZMaps.find x m = Some e.
Proof.
  split; [apply ZMaps.find_1|apply ZMaps.find_2].
Qed.
  
Lemma not_find_in_iff : forall (A : Type) (m : ZMaps.t A) (x : ZMaps.key), ~ ZMaps.In x m <-> ZMaps.find x m = None.
Proof.
  split; intros.
  rewrite eq_option_alt. intro e. rewrite <- find_mapsto_iff.
  split; try discriminate. intro H'; elim H; exists e; auto.
  intros (e,He).
  assert (ZMaps.MapsTo x e m <-> ZMaps.find x m = Some e) as H'.
    apply find_mapsto_iff.
  unfold ZMaps.MapsTo in H'.
  rewrite H in H'.
  apply H' in He.
  discriminate.
Qed.

Theorem find_empty_none : forall (A : Type) (x : ZMaps.key), ZMaps.find x (ZMaps.empty A) = None.
Proof.
  intros.
  apply not_find_in_iff.
  intros (e,Hc).
  assert (ZMaps.Empty (ZMaps.empty A)).
    apply ZMaps.empty_1.
  unfold ZMaps.Empty, ZMaps.Raw.Proofs.Empty in H.
  assert (~ ZMaps.Raw.MapsTo x e (ZMaps.this (ZMaps.empty A))).
    apply H.
  tauto.
Qed.

Theorem not_in_notmap : forall (A : Type) (xs : ZMaps.t A) (x  : ZMaps.key),
  ~ ZMaps.In x xs <-> forall e, ~ ZMaps.MapsTo x e xs.
  split; intros.
    intro.
      apply not_find_in_iff in H.
      apply ZMaps.find_1 in H0. rewrite H in H0. discriminate.
    apply not_find_in_iff.
    apply eq_option_alt.
    split; intros.
      apply ZMaps.find_2 in H0.
      now apply H in H0.

      discriminate.
Qed.

Theorem find_add_none : forall (A : Type) (xs : ZMaps.t A) (x a : ZMaps.key) (e : A),
  ZMaps.find a (ZMaps.add x e xs) = None <-> a <> x /\ ZMaps.find a xs = None.
  split; intros.
    split.
      apply not_find_in_iff in H.
      rewrite not_in_notmap in H.
      intro.
        assert (ZMaps.MapsTo a e (ZMaps.add x e xs)).
          rewrite H0.  now apply ZMaps.add_1.
        now apply H in H1.

        apply not_find_in_iff.
        apply not_find_in_iff in H.
        rewrite not_in_notmap in H.
        apply not_in_notmap; intros.
        assert (x = a \/ x <> a). tauto.
        destruct H0; intros; intro.
          assert (ZMaps.MapsTo a e (ZMaps.add x e xs)).
            rewrite H0; now apply ZMaps.add_1. now apply H in H2.
          assert (ZMaps.MapsTo a e0 (ZMaps.add x e xs)).
            apply ZMaps.add_2. assumption. assumption.
            now apply H in H2.
    destruct H as [Hne Hnf].
    apply eq_option_alt; split; intros.
      apply not_find_in_iff in Hnf; rewrite not_in_notmap in Hnf.
      assert (ZMaps.MapsTo a e0 xs).
        apply ZMaps.add_3 with (x := x) (e' := e).
          congruence.
          now apply ZMaps.find_2.
          now apply Hnf in H0.
        discriminate.
Qed.

Theorem negcl_domset'_1 : forall (cl : clause) (xs : list ivar) (x : ivar),
  InA eq x xs -> forall s, ZMaps.find x (negcl_domset' cl xs) = Some s -> dom_equal (dom_from_negclause x cl) s.
Proof.
  intros cl xs x; intro.
  remember (dom_from_negclause x cl) as dom.
  induction xs.
    now unfold In in H.
    apply InA_cons in H.

    unfold negcl_domset'; fold negcl_domset'.
    remember (negcl_domset' cl xs) as dset.
    intros; destruct H.

    assert (ZMaps.find x (ZMaps.add x dom dset) = Some dom).
      apply ZMaps.find_1; now apply ZMaps.add_1.
    rewrite <- H in H0. rewrite <- Heqdom in H0. rewrite H0 in H1.
    inversion H1.
    unfold dom_equal; tauto.

    assert (a = x \/ a <> x). tauto.
    destruct H1.
      rewrite H1 in H0; rewrite <- Heqdom in H0.
      assert (ZMaps.find x (ZMaps.add x dom dset) = Some dom).
        apply ZMaps.find_1; now apply ZMaps.add_1.
      rewrite H0 in H2.
      inversion H2.
      unfold dom_equal; tauto.

      apply IHxs. assumption.
      apply find_mapsto_iff.
      apply find_mapsto_iff in H0.
      apply ZMaps.add_3 with (x := a) (e' := (dom_from_negclause a cl)).
        assumption. assumption.
Qed.

Theorem not_in_cons : forall (A : Type) (a x : A) (xs : list A),
  ~ In a (cons x xs) <-> a <> x /\ ~ In a xs.
Proof.
  intros.
    split; intros.
      split; intro; subst.
        assert (In x (cons x xs)). apply in_eq.
        tauto.
        apply in_cons with (a := x) in H0.
        tauto.
      intro.
        destruct H.
        apply in_inv in H0; destruct H0.
          rewrite H0 in H; tauto. tauto.
Qed.
      
Theorem negcl_domset'_2 : forall (cl : clause) (xs : list ivar) (x : ivar),
  ~ In x xs -> (ZMaps.find x (negcl_domset' cl xs) = None).
Proof.
  intros; induction xs.
    unfold negcl_domset'; apply find_empty_none.

    apply not_in_cons in H; destruct H.
    unfold negcl_domset'; fold negcl_domset'.
    apply IHxs in H0.
    apply find_add_none. tauto.
Qed.

Theorem negcl_domset'_3 : forall (cl : clause) (xs : list ivar) (x : ivar),
  (ZMaps.find x (negcl_domset' cl xs) = None) -> ~ InA eq x xs.
Proof.
  intros cl xs x; induction xs.
    intros.  rewrite InA_nil. tauto.

  unfold negcl_domset'; fold negcl_domset'; simpl.
  intros.
    intro. apply InA_cons in H0.
    remember (negcl_domset' cl xs) as dset.
    apply find_add_none in H; destruct H.
    destruct H0.
      tauto.
    now apply IHxs in H0.
Qed.

Definition negcl_domset (cl : clause) :=
  negcl_domset' cl (ZSets.elements (clause_varset cl)).
  
Definition dom_from_domset (ds : domset) (x : ivar) :=
  match ZMaps.find x ds with
  | None => dom_unconstrained
  | Some d => d
  end.

Definition is_negcl_domset (ds : domset) (cl : clause) :=
  forall (x : ivar), dom_equal (dom_from_negclause x cl) (dom_from_domset ds x).

Definition is_negcl_domset_db (ds : domset) (cl : clause) :=
  forall x, (db_from_negclause x cl) = (fst (dom_from_domset ds x)).

Theorem dom_from_domset_equiv : forall (cl : clause),
  is_negcl_domset (negcl_domset cl) cl.
Proof.
  unfold is_negcl_domset; intros; unfold dom_from_domset, negcl_domset.
  remember (ZSets.elements (clause_varset cl)) as elts.
  remember (negcl_domset' cl elts) as dset.
  assert (~ mem (clause_varset cl) x \/ mem (clause_varset cl) x).
    tauto.
  destruct H.

  assert (H' := H).
  apply not_invars_uncon in H'.
  unfold mem in H.
  assert (ZMaps.find x dset = None).
    rewrite Heqdset; apply negcl_domset'_2.
  rewrite <- ZSets.elements_spec1 in H.
  intro; apply In_InA with (eqA := eq) in H0. rewrite Heqelts in H0. tauto.
  apply Z_as_OT.eq_equiv.
  rewrite H0.
  assert (dom_is_unconstrained dom_unconstrained).
    apply dom_unconstrained_is_uncon.
  unfold dom_is_unconstrained in *.
  unfold dom_equal; intros.
  split; intros; [apply H1 | apply H'].
  
  assert (H' := H); apply in_varset_iff_invars in H'.
  unfold mem in H.
  remember (ZMaps.find x dset) as dom_x.
  destruct dom_x.
  rewrite Heqdset in Heqdom_x.
  symmetry in Heqdom_x.
  apply ZSets.elements_spec1 in H.
  apply negcl_domset'_1 with (cl := cl) (s := d) in H.
  assumption.
  rewrite <- Heqelts. assumption.

  apply not_clausevar_iff_uncon in H'.
  tauto.

  rewrite Heqdset in Heqdom_x.
  symmetry in Heqdom_x; apply negcl_domset'_3 in Heqdom_x.
  rewrite Heqelts in Heqdom_x.
  apply ZSets.elements_spec1 in H. tauto.
Qed.

Theorem negcl_domset'_1db : forall (cl : clause) (xs : list ivar) (x : ivar),
  InA eq x xs -> forall s, ZMaps.find x (negcl_domset' cl xs) = Some s ->
    db_from_negclause x cl =  (fst s).
Proof.
  intros cl xs x; intro.
  remember (dom_from_negclause x cl) as dom.
  induction xs.
    now unfold In in H.
    apply InA_cons in H.

    unfold negcl_domset'; fold negcl_domset'.
    remember (negcl_domset' cl xs) as dset.
    intros; destruct H.

    assert (ZMaps.find x (ZMaps.add x dom dset) = Some dom).
      apply ZMaps.find_1; now apply ZMaps.add_1.
    rewrite <- H in H0. rewrite <- Heqdom in H0. rewrite H0 in H1.
    inversion H1; rewrite Heqdom; now rewrite dom_from_negclause_db.
    
    assert (a = x \/ a <> x). tauto.
    destruct H1.
      rewrite H1 in H0; rewrite <- Heqdom in H0.
      assert (ZMaps.find x (ZMaps.add x dom dset) = Some dom).
        apply ZMaps.find_1; now apply ZMaps.add_1.
      rewrite H0 in H2.
      inversion H2.
      rewrite Heqdom; now rewrite dom_from_negclause_db.

      apply IHxs. assumption.
      apply find_mapsto_iff.
      apply find_mapsto_iff in H0.
      apply ZMaps.add_3 with (x := a) (e' := (dom_from_negclause a cl)).
        assumption. assumption.
Qed.
     
Theorem dom_is_unconstrained_db : forall (d : dom),
  dom_is_unconstrained d -> (fst d) = (Unbounded, Unbounded).
Proof.
  unfold dom_is_unconstrained; intros.
  unfold sat_dom in H.
  assert (forall k, sat_dbound (fst d) k).
    apply H.
  unfold sat_dbound, sat_lb, sat_ub in H0.
  destruct d as (db, z); simpl; destruct db.
  destruct b, b0; simpl in *; try tauto; try discriminate.
  assert (Zle (Zsucc z0) z0).
    apply H0.
  assert False. omega. contradiction.

  assert (Zle z0 (Zpred z0)).
    apply H0.
  assert (Zlt (Zpred z0) z0).
    apply Zlt_pred.
  assert False. omega. contradiction.

  assert (Zle (Zsucc z1) z1).
    apply H0.
  assert False. omega. contradiction.
Qed.
  
Theorem dom_from_domset_db : forall (cl : clause),
  is_negcl_domset_db (negcl_domset cl) cl.
Proof.
  unfold is_negcl_domset_db; intros; unfold dom_from_domset, negcl_domset, dom_unconstrained.
  remember (ZSets.elements (clause_varset cl)) as elts.
  remember (negcl_domset' cl elts) as dset.
  assert (~ mem (clause_varset cl) x \/ mem (clause_varset cl) x).
    tauto.
  destruct H.

  assert (H' := H).
  apply not_invars_uncon in H'.
  apply dom_is_unconstrained_db in H'.
  rewrite dom_from_negclause_db in H'.
  unfold mem in H.
  assert (ZMaps.find x dset = None).
    rewrite Heqdset; apply negcl_domset'_2.
  rewrite <- ZSets.elements_spec1 in H.
  intro; apply In_InA with (eqA := eq) in H0. rewrite Heqelts in H0. tauto.
  apply Z_as_OT.eq_equiv.
  rewrite H0. now rewrite H'.
  
  assert (H' := H); apply in_varset_iff_invars in H'.
  unfold mem in H.
  remember (ZMaps.find x dset) as dom_x.
  destruct dom_x.
  rewrite Heqdset in Heqdom_x.
  symmetry in Heqdom_x.
  apply ZSets.elements_spec1 in H.
  apply negcl_domset'_1db with (xs := elts).
  now rewrite Heqelts. assumption.

  apply not_clausevar_iff_uncon in H'.
  tauto.

  rewrite Heqdset in Heqdom_x.
  symmetry in Heqdom_x; apply negcl_domset'_3 in Heqdom_x.
  rewrite Heqelts in Heqdom_x.
  apply ZSets.elements_spec1 in H. tauto.
Qed.

Definition domfun := ivar -> dom.
Definition eval_domfun (f : domfun) (theta : asg) :=
  forall x : ivar, sat_dom (f x) (eval_ivar x theta).

Definition is_negcl_domfun (f : domfun) (cl : clause) :=
  forall x : ivar, dom_equal (f x) (dom_from_negclause x cl).

Definition meet_domfun (f : domfun) (g : domfun) (x : ivar) := dom_meet (f x) (g x).

(*
Record DomCheck : Type := mkDomCheck
  { T : Type ;
    eval : T -> asg -> Prop ;
    check : T -> domfun -> bool ;
    check_valid : 
      forall (x : T) (f : domfun) (cl : clause),
      is_negcl_domfun f cl /\ check x f = true ->
        implies (eval x) (eval_clause cl) }.
*)

(*
Definition dombounded (C : DomCheck) : Type :=
  (domfun * C.(T))%type.
Definition dombounded_eval (C : DomCheck) (x : dombounded C) (theta : asg) :=
  eval_domfun (fst x) theta /\ C.(eval) (snd x) theta.
Definition dombounded_check (C : DomCheck) (x : dombounded C) (f : domfun) :=
  C.(check) (snd x) (fun v => dom_meet (f v) ((fst x) v)).
Theorem dombounded_check_valid : forall (C : DomCheck) (x : dombounded C) (f : domfun) (cl : clause),
  is_negcl_domfun f cl /\ dombounded_check C x f = true -> implies (dombounded_eval C x) (eval_clause cl).
Proof.
  intros.
    destruct H.
    unfold dombounded_check in H0.
    remember (fun v : ivar => dom_meet (f v) (fst x v)) as g.
    assert (C.(check) (snd x) f = true -> implies (eval C (snd x)) (eval_clause cl)).
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


Theorem eval_domfun_meet_iff : forall (f g : domfun) (theta : asg),
  eval_domfun (fun x => dom_meet (f x) (g x)) theta <-> eval_domfun f theta /\ eval_domfun g theta.
Proof.
  unfold eval_domfun; intros; split; intros.
  split; intros;
    [apply dom_meet_iff with (dy := g x) | apply dom_meet_iff with (dx := f x)]; apply H.
  destruct H as [Hf Hg]; rewrite dom_meet_iff; split; [apply Hf | apply Hg].
Qed.

*)
