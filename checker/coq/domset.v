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

Theorem InA_InB_iff : forall (A : Type) eqA eqB (xs : list A),
  (forall x y, eqA x y <-> eqB x y) -> (forall y, InA eqA y xs <-> InA eqB y xs).
Proof.
  intros; induction xs.
    repeat (rewrite InA_nil); tauto.

    repeat (rewrite InA_cons); now rewrite IHxs, H.
Qed.

Theorem not_InA_cons : forall (A : Type) eqA (a x : A) (xs : list A),
  ~ InA eqA a (cons x xs) <-> ( ~ eqA a x) /\ ~ InA eqA a xs.
Proof.
  intros; simpl.

  split; intros.
  split; intro.
  now apply InA_cons_hd with (eqA := eqA) (x := a) (y := x) (l := xs) in H0.
  now apply InA_cons_tl with (eqA := eqA) (x := a) (y := x) (l := xs) in H0.
  
  destruct H.
  intro. apply InA_cons in H1.
  destruct H1; tauto.
Qed.

Theorem eq_key_elt_iff_eq : forall B a b, ZMaps.eq_key_elt (elt := B) a b <-> a = b.
Proof.
  intros; unfold ZMaps.eq_key_elt, ZMaps.Raw.Proofs.PX.eqke; intros.
  destruct a, b; simpl.
    split; intros; [ destruct H; now rewrite H, H0 | inversion H; tauto].
Qed.
 
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

Definition var_db (ds : domset) (x : ivar) := fst (var_dom ds x).

Definition sat_domset (ds : domset) (x : ivar) (k : Z) :=
  sat_dom (var_dom ds x) k.

Theorem sat_domset_alt : forall (ds : domset) (x : ivar) (k : Z),
  sat_domset ds x k <->
    forall (d : dom), ZMaps.MapsTo x d ds -> sat_dom d k.
Proof.
  intros; unfold sat_domset, var_dom; split; intros.

    apply ZMaps.find_1 in H0; now rewrite H0 in H.

    remember (ZMaps.find x ds) as fx.
    destruct fx.
      apply H; now apply ZMaps.find_2.
      now apply dom_unconstrained_is_uncon.
Qed.  

Theorem sat_domset_iff_doms : forall (ds : domset) (x : ivar) (k : Z),
  sat_domset ds x k <-> sat_doms (ZMaps.elements ds) x k.
Proof.
  intros.
  rewrite sat_domset_alt.
  rewrite sat_doms_alt.
  split; intros.
    apply H, ZMaps.elements_2, InA_InB_iff with (eqB := eq), InA_eq_iff_In.
    intros; apply eq_key_elt_iff_eq.
    assumption.

    apply ZMaps.elements_1, InA_InB_iff with (eqB := eq), InA_eq_iff_In in H0.
    now apply H.
    apply eq_key_elt_iff_eq.
Qed.
  
Definition eval_domset (ds : domset) (theta : asg) := forall x : ivar,
  sat_domset ds x (eval_ivar x theta).

Definition domset_unsat (ds : domset) := forall theta, ~ eval_domset ds theta.

Fixpoint doms_unsatb (elts : list (ivar * dom)) :=
  match elts with
  | nil => false
  | cons (x, dom) elts' => (dom_unsatb dom) || (doms_unsatb elts')
  end.


Theorem eval_domset_alt : forall (ds : domset) (theta : asg),
  eval_domset ds theta <->
    (forall (x : ivar) (d : dom), ZMaps.MapsTo x d ds -> eval_dom (x, d) theta).
Proof.
  intros; unfold eval_domset; split; intros.
  unfold eval_dom; simpl.
  assert (sat_domset ds x (eval_ivar x theta)). apply H.
  unfold sat_domset, var_dom in H1.
  apply ZMaps.find_1 in H0.
  now rewrite H0 in H1.

  unfold sat_domset, var_dom.
  remember (ZMaps.find x ds) as fx.
  destruct fx.
    symmetry in Heqfx; apply ZMaps.find_2 in Heqfx; now apply H in Heqfx.
    apply dom_unconstrained_is_uncon.
Qed.
  
(*
Definition domset_unsatb (ds : domset) := doms_unsatb (ZMaps.elements ds).
Lemma domset_unsatb_iff : forall (ds : domset), domset_unsatb ds = true <-> domset_unsat ds.
Proof.
  intros; remember (ZMaps.elements ds) as elts; induction elts.
  unfold domset_unsatb, doms_unsatb; rewrite <- Heqelts.
  unfold domset_unsat; split; intros; try discriminate.
  unfold eval_domset in H.
*)
  
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

Definition bounds_domset (bs : list model_bound) :=
  negcl_domset (negclause_of_bounds bs).
 
Theorem InA_eq_key_elt_iff_In : forall (B : Type) (xs : list (Z * B)) (y : (Z * B)),
  InA (ZMaps.eq_key_elt (elt := B)) y xs <-> In y xs.
Proof.
  intros.
      
  rewrite <- InA_eq_iff_In.
  split; intros.
    apply InA_InB_iff with (eqB := (ZMaps.eq_key_elt (elt := B))).
    intros; symmetry; now apply eq_key_elt_iff_eq. assumption.

    apply InA_InB_iff with (eqB := (ZMaps.eq_key_elt (elt := B))).
      intros; tauto.
    apply InA_InB_iff with (eqB := (ZMaps.eq_key_elt (elt := B))) in H.
    assumption. intros. rewrite eq_key_elt_iff_eq. tauto.
Qed.
    
Definition negclause_of_domset (ds : domset) :=
  negclause_of_doms (ZMaps.elements ds).

Theorem eval_domset_iff_doms : forall (ds : domset) (theta : asg),
  eval_domset ds theta <-> eval_doms (ZMaps.elements ds) theta.
Proof.
  intros.
  rewrite eval_domset_alt, eval_doms_alt.
  split; intros.
    apply InA_eq_iff_In, InA_InB_iff with (eqB := (ZMaps.eq_key_elt (elt := dom))) in H0.
    destruct d; simpl; apply ZMaps.elements_2 in H0.
    now apply H.
    intros; now rewrite eq_key_elt_iff_eq.

    apply H.
    apply InA_eq_iff_In, InA_InB_iff with (eqB := ZMaps.eq_key_elt (elt := dom)).
      intros; now rewrite eq_key_elt_iff_eq.
    now apply ZMaps.elements_1.
Qed.
 
Theorem sat_negclause_domset_iff : forall (ds : domset) (x : ivar) (k : Z),
  sat_domset ds x k <-> sat_negclause (negclause_of_domset ds) x k.
Proof.
  intros.
  unfold negclause_of_domset.
  rewrite sat_domset_iff_doms.
  apply sat_negclause_doms_iff.
Qed.

Theorem negclause_of_domset_valid : forall (ds : domset) (theta : asg),
  eval_domset ds theta <-> ~ eval_clause (negclause_of_domset ds) theta.
Proof.
  intros.
    unfold negclause_of_domset.
    rewrite eval_domset_iff_doms.
    apply negclause_of_doms_valid.
Qed.

Theorem negcl_domset_is_negcl_domfun : forall (cl : clause),
  is_negcl_domfun (var_dom (negcl_domset cl)) cl.
Proof.
  intros; assert (is_negcl_domset (negcl_domset cl) cl).
    apply dom_from_domset_equiv.
  unfold is_negcl_domset, dom_equal in H.
  unfold is_negcl_domfun.
  intros; rewrite H; now unfold dom_from_domset, var_dom.
Qed.

Theorem negcl_domset_is_negcl_domfun_db : forall (cl : clause),
  is_negcl_domfun_db (var_dom (negcl_domset cl)) cl.
Proof.
  intros; assert (is_negcl_domset_db (negcl_domset cl) cl).
    apply dom_from_domset_db.
  unfold is_negcl_domset_db in H.
  unfold is_negcl_domfun_db.
  intros; rewrite H; now unfold dom_from_domset, var_dom.
Qed.

Theorem sat_dom_negclause_iff : forall (ds : list (ivar * dom)) (x : ivar) (k : Z),
  sat_dom (dom_from_negclause x (negclause_of_doms ds)) k
    <-> sat_doms ds x k.
Proof.
  intros; induction ds.
    unfold negclause_of_doms, sat_doms, dom_from_negclause.
      split; [trivial | intros; apply dom_unconstrained_is_uncon].

    destruct a; unfold sat_doms, negclause_of_doms; fold sat_doms; fold negclause_of_doms; simpl.
    rewrite app_dom_from_negclause_iff.
    rewrite IHds.
    apply and_iff_compat_r.
    assert (x <> i <-> i <> x) as Hsd. split; intros; congruence.
    rewrite Hsd. rewrite sat_negclause_dom_iff.
    now rewrite sat_dom_negclause_iff.
Qed.

Theorem negcl_of_domset_equiv : forall (ds : domset),
  is_negcl_domfun (var_dom ds) (negclause_of_domset ds).
Proof.
  intros.
    unfold is_negcl_domfun; intros.
    assert (H := sat_negclause_domset_iff ds x k).
    rewrite domain.sat_dom_negclause_iff.
    now rewrite H.
Qed.

Theorem notin_eqkey_doms_uncon : forall (ds : list (ivar * dom)) (x : ivar) (d : dom),
  ~ InA (ZMaps.eq_key (elt := dom)) (x, d) ds ->
    db_of_doms x ds = (Unbounded, Unbounded).
Proof.
  intros.
  induction ds.
  unfold db_of_doms; now simpl.

  unfold db_of_doms; simpl; fold db_of_doms.
  assert (~ ZMaps.eq_key (x, d) a).
    intro.
    now apply InA_cons_hd with (l := ds) (x := (x, d)) (y := a) in H0.
  assert (~ InA (ZMaps.eq_key (elt := dom)) (x, d) ds).
    intro.
    now apply InA_cons_tl with (l := ds) (x := (x, d)) (y := a) in H1.
    destruct a; simpl.
  apply IHds in H1.
  rewrite H1.
  unfold ZMaps.eq_key, ZMaps.Raw.Proofs.PX.eqk in H0; simpl in H0.
  remember (ivar_eqb x i) as xi; symmetry in Heqxi; destruct xi.
  now apply ivar_eqb_iff_eq in Heqxi. trivial.
Qed.

Lemma InA_eqkey_x_iff : forall (ds : list (ivar * dom)) (x : ivar) (d d' : dom),
  InA (ZMaps.eq_key (elt := dom)) (x, d) ds <-> InA (ZMaps.eq_key (elt := dom)) (x, d') ds.
Proof.
  intros.
  unfold ZMaps.eq_key, ZMaps.Raw.Proofs.PX.eqk; simpl.

  induction ds.
  now repeat (rewrite InA_nil).

  repeat (rewrite InA_cons).
  rewrite IHds.
  apply or_iff_compat_r. simpl. tauto.
Qed.
    
Theorem nodup_dom_of_doms_db_eq : forall (ds : list (ivar * dom)) (x : ivar) (d : dom),
  NoDupA (ZMaps.eq_key (elt := dom)) ds ->
    In (x, d) ds -> db_of_doms x ds = fst d.
Proof.
  intros.
  induction ds.
    now unfold In in H0.
    apply in_inv in H0.
    unfold db_of_doms; simpl; fold db_of_doms.
    destruct a; simpl in *.
    inversion H.
    assert (db_of_doms i ds = (Unbounded, Unbounded)).
      now apply notin_eqkey_doms_uncon with (d := d0).
    remember (ivar_eqb x i) as xi; symmetry in Heqxi; destruct xi.
    rewrite ivar_eqb_iff_eq in Heqxi.
    rewrite <- Heqxi in *.
    rewrite H5.
    destruct H0.
    inversion H0.
    unfold db_meet, bound_max, bound_min; destruct d; destruct d; destruct b, b0; now simpl.
    apply In_InA with (eqA := (ZMaps.eq_key (elt := dom))) in H0.
    now apply InA_eqkey_x_iff with (d' := d0) in H0.
    unfold ZMaps.eq_key; split; eauto.
    assert (x <> i). intro; rewrite <- ivar_eqb_iff_eq in H6; congruence.
    destruct H0; try congruence.
    apply IHds. assumption. assumption.
Qed.

Theorem notin_eqk_iff_notin : forall (ds : list (ivar * dom)) (x : ivar) (d : dom),
  ~ InA (ZMaps.eq_key (elt := dom)) (x, d) ds <-> (forall (d' : dom), ~ InA (ZMaps.eq_key_elt (elt := dom)) (x, d') ds).
Proof.
  intros.
  induction ds.

  split; intros; now rewrite InA_nil.
  rewrite not_InA_cons.
  split; intros.
    rewrite not_InA_cons.
    destruct H.
    split.

    destruct a; simpl.
    unfold ZMaps.eq_key, ZMaps.Raw.Proofs.PX.eqk in H; simpl in H.
    unfold ZMaps.eq_key_elt, ZMaps.Raw.Proofs.PX.eqke; simpl.
    tauto.

    now apply IHds.
    assert (forall d', ~ (ZMaps.eq_key_elt (elt := dom)) (x, d') a /\ ~ InA (ZMaps.eq_key_elt (elt := dom)) (x, d') ds).
      intros; now apply not_InA_cons.
    apply forall_and in H0; destruct H0.
    split.
    unfold ZMaps.eq_key, ZMaps.Raw.Proofs.PX.eqk; simpl.
    assert (H' := H0 (snd a)).
    unfold ZMaps.eq_key_elt, ZMaps.Raw.Proofs.PX.eqke in H'; simpl in *.
    tauto.
    apply IHds. intros. apply H1.
Qed.

Theorem notin_notin_elts : forall (ds : domset) (x : ivar) (d : dom),
  ~ ZMaps.In x ds -> ~ InA (ZMaps.eq_key (elt := dom)) (x, d) (ZMaps.elements ds).
Proof.
  intros.
  apply notin_eqk_iff_notin.
  intros.
  intro.
  apply ZMaps.elements_2 in H0.
  rewrite not_find_in_iff in H.
  apply ZMaps.find_1 in H0.
  congruence.
Qed.

Theorem db_of_doms_domset_eq : forall (ds : domset) (x :ivar),
  fst (var_dom ds x) = db_of_doms x (ZMaps.elements ds).
Proof.
  intros.
    assert (Hnd := ZMaps.elements_3w ds).
    assert (H := negcl_domset_is_negcl_domfun_db).
    unfold var_dom.
    remember (ZMaps.find x ds) as fx; symmetry in Heqfx.

    destruct fx.
    apply ZMaps.find_2, ZMaps.elements_1 in Heqfx.
    rewrite InA_InB_iff with (eqB := eq) in Heqfx; try apply eq_key_elt_iff_eq.
    rewrite InA_eq_iff_In in Heqfx.
    rewrite nodup_dom_of_doms_db_eq with (d := d); try trivial.

    rewrite notin_eqkey_doms_uncon with (d := dom_unconstrained).
    rewrite <- not_find_in_iff in Heqfx.
    unfold dom_unconstrained; now simpl.
    rewrite <- not_find_in_iff in Heqfx.
    now apply notin_notin_elts.
Qed.
  
Theorem negcl_of_domset_db_equiv : forall (ds : domset),
  is_negcl_domfun_db (var_dom ds) (negclause_of_domset ds).
Proof.
  unfold is_negcl_domfun_db; intros.
  unfold negclause_of_domset.
  rewrite negclause_of_doms_db_eq.
  apply db_of_doms_domset_eq.
Qed.
     
Definition dombounded T : Type :=
  (domset * T)%type.
Definition dombounded_eval (T : Type) (eval : T -> asg -> Prop) (x : dombounded T) (theta : asg) :=
  eval_domset (fst x) theta /\ eval (snd x) theta.
Definition dombounded_check (T : Type) (check : T -> domfun -> bool) (x : dombounded T) (f : domfun) :=
  check (snd x) (domfun_meet f (var_dom (fst x))).
Definition dombounded_db_check (T : Type) (check : T -> dbfun -> bool) (x : dombounded T) (f : dbfun) :=
  check (snd x) (dbfun_meet f (var_db (fst x))).
Theorem dombounded_check_valid : forall (C : Constraint) (Ch : DomCheck C) (x : dombounded C.(T)) (f : domfun) (cl : clause),
  is_negcl_domfun f cl /\ dombounded_check C.(T) (dc_check C Ch) x f = true -> implies (dombounded_eval C.(T) C.(eval) x) (eval_clause cl).
Proof.
  intros.
    destruct H.
    unfold dombounded_eval, implies;
    unfold dombounded_check in H0;
    destruct x; simpl in *; intros.
    destruct H1.

    remember (negclause_of_domset d) as bcl.
    remember (domfun_meet f (var_dom d)) as fg.
    assert (is_negcl_domfun fg (cl ++ bcl)).
      rewrite Heqfg, Heqbcl; apply app_negcl_domfun_if.
      split; try assumption.
    apply negcl_of_domset_equiv.
    assert (implies (C.(eval) t) (eval_clause (List.app cl bcl))).
    apply (dc_check_valid C Ch) with (f := fg); split; assumption.
     
    unfold implies in H4.
    assert (Happ := H4 theta).
    apply Happ in H2.
    rewrite app_clause_or in H2.
    destruct H2; [assumption | rewrite Heqbcl in H2; now apply negclause_of_domset_valid in H2].
Qed.

Theorem dombounded_db_check_valid : forall (C : Constraint) (Ch : DomDBCheck C) (x : dombounded C.(T)) (f : dbfun) (cl : clause),
  is_negcl_dbfun f cl /\ dombounded_db_check C.(T) (db_check C Ch) x f = true -> implies (dombounded_eval C.(T) C.(eval) x) (eval_clause cl).
Proof.
  intros.
    destruct H.
    unfold dombounded_eval.
    unfold implies; intros.
    unfold dombounded_db_check in H0.
    remember (negclause_of_domset (fst x)) as bcl.
    assert (is_negcl_dbfun (var_db (fst x)) bcl).
      rewrite Heqbcl. apply negcl_of_domset_db_equiv.
    remember (dbfun_meet f (var_db (fst x))) as fg.
    assert (is_negcl_dbfun fg (cl ++ bcl)).
    rewrite Heqfg, Heqbcl; apply app_negcl_dbfun_if.
    split. assumption. apply negcl_of_domset_db_equiv.
     
    assert (is_negcl_dbfun fg (List.app cl bcl) /\ (db_check C Ch) (snd x) fg = true ->
      implies (C.(eval) (snd x)) (eval_clause (List.app cl bcl))) as Cvalid.
      intros. apply (db_check_valid C Ch) with (f := fg).
      tauto.
    destruct H1.
    unfold implies in Cvalid.
    assert (eval_clause (List.app cl bcl) theta).
      apply Cvalid. split. assumption. assumption. assumption.
    unfold is_negcl_dbfun in H3.
    rewrite app_clause_or in H5.
    destruct H5; try assumption.
    rewrite Heqbcl in H5.
    now apply negclause_of_domset_valid in H5.
Qed.

Definition DomboundedConstraint (C : Constraint) := mkConstraint
  (dombounded C.(T)) (dombounded_eval C.(T) C.(eval)).
Definition DomboundedCheck (C : Constraint) (D : DomCheck C) :=
  mkDomCheck (DomboundedConstraint C)
    (dombounded_check C.(T) (dc_check C D))
    (dombounded_check_valid C D).

Definition DomboundedDBCheck (C : Constraint) (D : DomDBCheck C) :=
  mkDomDBCheck (DomboundedConstraint C)
    (dombounded_db_check C.(T) (db_check C D))
    (dombounded_db_check_valid C D).

Definition check_from_dcheck (C : Constraint) (D : DomCheck C) (x : C.(T)) (cl : clause) :=
  (dc_check C D) x (var_dom (negcl_domset cl)).
Theorem check_from_dcheck_valid : forall (C : Constraint) (D : DomCheck C) (x : C.(T)) (cl : clause),
  check_from_dcheck C D x cl = true ->
    implies (C.(eval) x) (eval_clause cl).
Proof.
  unfold check_from_dcheck; intros.
  remember (var_dom (negcl_domset cl)) as f.
  apply (dc_check_valid C D) with (f := f).
  split; [rewrite Heqf; apply negcl_domset_is_negcl_domfun | assumption].
Qed.

Definition check_from_dbcheck (C: Constraint) (D : DomDBCheck C) (x : C.(T)) (cl : clause) :=
  (db_check C D) x (var_db (negcl_domset cl)).
Theorem check_from_dbcheck_valid : forall (C : Constraint) (D : DomDBCheck C) (x : C.(T)) (cl : clause),
  check_from_dbcheck C D x cl = true ->
    implies (C.(eval) x) (eval_clause cl).
Proof.
  unfold check_from_dbcheck; intros.
  remember (var_db (negcl_domset cl)) as f.
  apply (db_check_valid C D) with (f := f).
  split; [rewrite Heqf; apply negcl_domset_is_negcl_domfun_db | assumption].
Qed.

Definition CheckOfDomCheck (C : Constraint) (D : DomCheck C) :=
  mkChecker C (check_from_dcheck C D) (check_from_dcheck_valid C D).

Definition CheckOfDomDBCheck (C : Constraint) (D : DomDBCheck C) :=
  mkChecker C (check_from_dbcheck C D) (check_from_dbcheck_valid C D).


Definition check_tauto_var_dfun (f : domfun) (v : ivar) :=
  dom_unsatb (f v).
Theorem check_tauto_var_dfun_valid : forall (f : domfun) (cl : clause) (v : ivar) (theta : asg),
  is_negcl_domfun f cl ->
    check_tauto_var_dfun f v = true -> eval_clause cl theta.
Proof.
  intros.
  assert (eval_clause cl theta \/ ~ eval_clause cl theta). tauto.
  destruct H1; try assumption.
  apply negcl_domfun_valid with (x := v) (theta := theta) in H.
  unfold check_tauto_var_dfun in H0.
  rewrite dom_unsatb_unsat in H0. now apply H0 in H.
  assumption.
Qed.

Fixpoint check_tauto_dfun (vs : list ivar) (f : domfun) :=
  match vs with
  | nil => false
  | cons v vs' => (check_tauto_var_dfun f v) || (check_tauto_dfun vs' f )
  end.

Theorem check_tauto_dfun_valid' : forall (f : domfun) (cl : clause) (vs : list ivar) (theta : asg),
  is_negcl_domfun f cl ->
    check_tauto_dfun vs f = true -> eval_clause cl theta.
Proof.
  intros; induction vs; intros.
  now unfold check_tauto_dfun.

  unfold check_tauto_dfun in H0; fold check_tauto_dfun in H0.
  rewrite orb_true_iff in H0.
  destruct H0 ; [ apply check_tauto_var_dfun_valid with (f := f) (v := a); assumption | apply IHvs; assumption ].
Qed.

Definition eval_tauto_hint (vs : list ivar) (theta : asg) := True.

Theorem check_tauto_dfun_valid : forall (vs : list ivar) (f : domfun) (cl : clause),
  is_negcl_domfun f cl /\
    check_tauto_dfun vs f = true -> implies (eval_tauto_hint vs) (eval_clause cl).
Proof.
  intros. unfold implies, eval_tauto_hint; intros.
  now apply check_tauto_dfun_valid' with (f := f) (theta := theta) (vs := vs).
Qed.

Definition HintTauto := mkConstraint (list ivar) eval_tauto_hint.

Definition HintTautoDom : DomCheck HintTauto :=
  mkDomCheck HintTauto (check_tauto_dfun) (check_tauto_dfun_valid).

Definition HintTautoDomCheck : Checker (DomboundedConstraint HintTauto) :=
  CheckOfDomCheck (DomboundedConstraint HintTauto) (DomboundedCheck HintTauto HintTautoDom).

Definition check_tauto_dbnd (ds : domset) (cl : clause) :=
  (check (DomboundedConstraint HintTauto) HintTautoDomCheck) (ds, ZSets.elements (clause_varset cl)) cl.