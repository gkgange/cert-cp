Require Import ZArith.
Require Import range.
Require Import Bool.
Require Import map.

Require Import assign.

Require range_properties.

Definition dom := (dbound * zset.zset)%type.

Definition dom_unconstrained : dom := ((Unbounded, Unbounded), zset.empty).
Definition dom_const (k : Z) : dom := ((Bounded k, Bounded k), zset.empty).
Definition dom_neq (k : Z) : dom := ((Unbounded, Unbounded), zset.add zset.empty k).
Definition dom_le (k : Z) : dom := ((Unbounded, Bounded k), zset.empty).
Definition dom_ge (k : Z) : dom := ((Bounded k, Unbounded), zset.empty).
Definition dom_range (l : Z) (u : Z) : dom := ((Bounded l, Bounded u), zset.empty).
Definition dom_contra : dom := ((Bounded 1, Bounded 0), zset.empty).

Definition sat_dom (d : dom) (k : Z) :=
  sat_dbound (fst d) k /\ ~ zset.mem (snd d) k.

Definition satb_dom (d : dom) (k : Z) :=
  satb_dbound (fst d) k && negb (zset.memb (snd d) k).

Lemma satb_dom_iff : forall d k, satb_dom d k = true <-> sat_dom d k.
Proof.
  intros; unfold sat_dom, satb_dom; repeat (tsimpl || range_properties.db_simpl || zset.zset_simpl).
Qed.
  
Definition dom_equal (dx dy : dom) := forall k : Z,
  sat_dom dx k <-> sat_dom dy k.

Definition eval_dom (d : (ivar * dom)) (theta : valuation) :=
  sat_dom (snd d) (theta (fst d)).

Lemma eval_dom_uncon : forall (x : ivar) (theta : valuation),
  eval_dom (x, dom_unconstrained) theta.
Proof.
  unfold dom_unconstrained, eval_dom; unfold sat_dom; simpl.
  unfold_satdb; intros.
  tsimpl.
  now apply zset.notmem_empty in H.
Qed.

Definition strict_domset := (map.zmap dom).
Definition domset := option strict_domset.

Definition domset_empty := Some (map.ZMaps.empty dom).

Definition dom_of_range (r : dbound) := (r, zset.empty).
Definition range_of_dom (d : dom) :=
  match d with
  | (r, _) => r
  end.

Definition eval_strict_domset ds theta :=
  forall x d, ZMaps.MapsTo x d ds -> eval_dom (x, d) theta.
Definition eval_domset ds theta :=
  match ds with
  | None => False
  | Some s => eval_strict_domset s theta
  end.

Definition var_dom ds x :=
  match ds with
  | None => dom_contra
  | Some s =>
    match ZMaps.find x s with
    | None => dom_unconstrained
    | Some d => d
    end
  end.

Definition term_dom ds x :=
  match x with
  | Ilit k => dom_const k
  | Ivar v => var_dom ds v
  end.

Definition db_from_dom x ds := fst (var_dom ds x).

Definition eval_domset_alt ds theta := forall (x : ivar), eval_dom (x, var_dom ds x) theta.

Definition dom_unsat (d : dom) := forall k, ~ sat_dom d k.

Lemma dom_contra_unsat : dom_unsat dom_contra.
Proof.
  unfold dom_unsat, dom_contra, sat_dom, sat_dbound; intros; tsimpl.
Qed.

Lemma eval_domset_equiv : forall ds theta, eval_domset ds theta <-> eval_domset_alt ds theta.
Proof.
  intros; unfold eval_domset, eval_strict_domset, eval_domset_alt, var_dom; tsimpl;
    destruct ds;
    try eqelim (ZMaps.find x t); zmap_simpl.

  now apply H.
  apply eval_dom_uncon.
  contradiction.

  intros; specialize (H x); eqelim (ZMaps.find x t); zmap_simpl.
  now rewrite <- H1.
  specialize (H 0).
  unfold eval_dom in H.
  now apply dom_contra_unsat in H.
Qed.

Lemma eval_domset_vardom : forall ds x theta, eval_domset ds theta -> eval_dom (x, var_dom ds x) theta.
Proof.
  intros ds x theta H; apply eval_domset_equiv in H; unfold eval_domset_alt in H; now apply H.
Qed.
Lemma db_from_dom_valid : forall ds x theta, eval_domset ds theta -> sat_dbound (db_from_dom x ds) (theta x).
Proof.
  intros; apply eval_domset_vardom with (x := x) (theta := theta) in H; now unfold eval_dom, sat_dom in H.
Qed.

Definition dom_leq dx dy := forall k, sat_dom dx k -> sat_dom dy k.

(*
Definition domset_leq ds ds' := forall theta, eval_domset ds theta -> eval_domset ds' theta.
Definition domset_leq_alt ds ds' := forall x, dom_leq (var_dom ds x) (var_dom ds' x).

Lemma domset_leq_equiv : forall ds ds', domset_leq ds ds' <-> domset_leq_alt ds ds'.
Proof.
  unfold domset_leq, domset_leq_alt; unfold dom_leq; intros; tsimpl.
  specialize (H (fun (y : ivar) => k)).
  remember (fun (y : ivar) => k) as theta.
  
  rewrite eval_domset_alt 
*)

Definition dom_meet dx dy :=
  (db_meet (fst dx) (fst dy), zset.union (snd dx) (snd dy)).

Lemma dom_meet_iff : forall dx dy k, sat_dom (dom_meet dx dy) k <-> sat_dom dx k /\ sat_dom dy k.
Proof.
  intros; unfold sat_dom; repeat (range_properties.db_simpl || tsimpl).

  assert (Hu := zset.mem_union_iff (snd dx) (snd dy) k); tauto.
  assert (Hu := zset.mem_union_iff (snd dx) (snd dy) k); tauto.
  assert (Hu := zset.mem_union_iff (snd dx) (snd dy) k); tauto.
Qed.

Lemma eval_dom_meet_iff : forall x d d' theta, eval_dom (x, dom_meet d d') theta <-> eval_dom (x, d) theta /\ eval_dom (x, d') theta.
Proof.
  intros; unfold eval_dom; simpl in *; apply dom_meet_iff.
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
        zset.zset_covers holes lb ub
      end
    end
  end.

Lemma unbounded_not_unsat_l : forall (u : bound) (z : zset.zset),
  dom_unsat ((Unbounded, u), z) -> False.
Proof.
  unfold dom_unsat; intros; destruct u; tsimpl.
   assert (sat_dom ((Unbounded, Unbounded), z) ((zset.zset_min_lb z 0) - 1)).
    unfold sat_dom; repeat (tsimpl || range_properties.db_simpl).
    apply zset.lt_min_notin_zset with (k := 0) in H0; tsimpl.
    now apply H in H0.

  assert (sat_dom ((Unbounded, Bounded z0), z) ((zset.zset_min_lb z z0) - 1)).
    unfold sat_dom; repeat (tsimpl || range_properties.db_simpl).
    unfold_satdb; tsimpl.
    assert (H' := zset.zset_min_lb_le z z0); tsimpl.
    apply zset.lt_min_notin_zset with (k := z0) in H0; tsimpl.
    now apply H in H0.
Qed. 

Lemma unbounded_not_unsat_r : forall (l : bound) (z : zset.zset),
  dom_unsat ((l, Unbounded), z) -> False.                                
Proof.
  intros; destruct l; tsimpl.
  now apply unbounded_not_unsat_l in H.

  unfold dom_unsat in H.
   assert (sat_dom ((Bounded z0, Unbounded), z) ((zset.zset_max_ub z z0) + 1)).
   unfold sat_dom; repeat (tsimpl || range_properties.db_simpl).
   unfold_satdb; tsimpl.
   assert (H' := zset.zset_max_ub_lb z z0); tsimpl.
   apply zset.max_lt_notin_zset with (k := z0) in H0; tsimpl.
   now apply H in H0.
Qed.

Theorem dom_unsatb_unsat : forall (d : dom),
  dom_unsatb d = true <-> dom_unsat d.
Proof.
  unfold dom_unsatb; intros; destruct d as (db, z); destruct db as (l, u); simpl; tsimpl.

  destruct l, u; tsimpl.
  assert (Hc := zset.zset_covers_spec z z0 z1).
  unfold dom_unsat; intros; intro; unfold sat_dom in H0; tsimpl.
  apply H2 with (k := k) in H; try assumption; contradiction.

  destruct l, u; tsimpl.
  now apply unbounded_not_unsat_l in H.
  now apply unbounded_not_unsat_l in H.
  now apply unbounded_not_unsat_r in H.

  apply zset.zset_covers_spec; intros.
  specialize (H k).
  
  apply Decidable.dec_not_not; intros.
    apply zset.mem_dec.

  assert (sat_dom (Bounded z0, Bounded z1, z) k).
  unfold sat_dom; unfold_satdb; repeat (tsimpl || range_properties.db_simpl).
  now apply H in H2.
Qed.

Definition apply_vardom (ds : domset) x d :=
  match ds with
  | None => None
  | Some s =>
    let d0 := var_dom ds x in
    let dM := dom_meet d0 d in
    if dom_unsatb dM then
      None
    else
      Some (ZMaps.add x dM s)
  end.

Lemma apply_vardom_1 : forall ds x d,
  forall theta,
    eval_domset ds theta -> eval_dom (x, d) theta -> eval_domset (apply_vardom ds x d) theta.
Proof.
  intros ds x d; unfold apply_vardom; ifelim; intros.

  apply (eval_domset_vardom (Some t) x) in H.
  rewrite dom_unsatb_unsat in H0.
  specialize (H0 (theta x)).
  rewrite dom_meet_iff in H0.
  tauto.
  
  contradiction.

  destruct ds; tsimpl.
  unfold eval_domset, eval_strict_domset in *; simpl; intros.
  eqelim (ZMaps.find x t); zmap_simpl.
  apply ZMapProperties.F.add_mapsto_iff in H2; destruct H2; destruct H2.

  rewrite <- H2.
  rewrite <- H3; apply eval_dom_meet_iff; split; tsimpl.

  now apply H.
  now apply H.

  apply ZMapProperties.F.add_mapsto_iff in H2; destruct H2; destruct H2.
  rewrite <- H2.
  rewrite <- H3; apply eval_dom_meet_iff; split; tsimpl.
  apply eval_dom_uncon.
  now apply H.
Qed.

Lemma apply_vardom_2l : forall ds x d theta,
  eval_domset (apply_vardom ds x d) theta -> eval_domset ds theta.
Proof.
  intros.
  unfold apply_vardom, eval_domset in *.
  destruct ds; ifelim; [contradiction | trivial | trivial].

  unfold eval_strict_domset in *; intros.
  assert (Heq := ivar_eq_dec x x0).
  destruct Heq.

  rewrite <- H2 in *; clear H2.
  
  unfold var_dom in *; eqelim (ZMaps.find x s); zmap_simpl.

  specialize (H x (dom_meet d0 d)).
  rewrite <- H2 in *; clear H2.
  assert (eval_dom (x, dom_meet d1 d) theta) as Hev.
    apply H. now apply ZMaps.add_1.
  rewrite eval_dom_meet_iff in Hev. tauto.

  apply H.
  apply ZMaps.add_2; assumption.
Qed.

Lemma eval_if_apply_vardom : forall ds x d theta, eval_dom (x, var_dom (apply_vardom ds x d) x) theta -> eval_dom (x, d) theta.
Proof.
  intros; unfold var_dom, apply_vardom in *.
  destruct ds; ifelim.

  now apply dom_contra_unsat in H.
  eqelim (ZMaps.find (elt:=dom) x (ZMaps.add x (dom_meet (var_dom (Some s) x) d) s)); zmap_simpl.
  apply ZMapProperties.F.add_mapsto_iff in H2; destruct H2; [trivial | tauto].
  destruct H0 as [Hl Hr]; rewrite <- Hr in H.
  now apply eval_dom_meet_iff in H.
  apply find_add_none in H2; destruct H2; congruence.
  now apply dom_contra_unsat in H.
Qed.
  
Lemma apply_vardom_2r : forall ds x d theta,
  eval_domset (apply_vardom ds x d) theta -> eval_dom (x, d) theta.
Proof.
  intros. apply eval_if_apply_vardom with (ds := ds).
  now apply eval_domset_vardom.
Qed.
  
Lemma apply_vardom_3 : forall ds x d, apply_vardom ds x d = None ->
  forall theta, eval_domset ds theta -> eval_dom (x, d) theta -> False.
Proof.
  unfold apply_vardom; intros; ifelim; tsimpl.
  rewrite dom_unsatb_unsat in H3.
  specialize (H3 (theta x)).
  assert (Hd := eval_dom_meet_iff x (var_dom ds x) d theta).
  destruct Hd.   
  assert (Hv := eval_domset_vardom ds x theta).
  rewrite H4 in *. tauto.

  destruct ds; [congruence | contradiction].
Qed.

Lemma eval_domset_empty : forall theta, eval_domset domset_empty theta.
Proof.
  unfold domset_empty, eval_domset, eval_strict_domset; intros.
  now apply ZMapProperties.F.empty_mapsto_iff in H.
Qed.


Ltac dom_simpl :=
  repeat (match goal with
    (* Boolean stuff *)
    | [ H : context[satb_dom _ _ = true] |- _ ] => rewrite <- satb_dom_iff in H
    | [ |- context[satb_dom _ _ = true] ] => rewrite <- satb_dom_iff
    | [ H : context[dom_unsatb _ = true] |- _ ] => rewrite <- dom_unsatb_unsat in H
    | [ |- context[dom_unsatb _ = true] ] => rewrite <- dom_unsatb_unsat
    (* Meet stuff *)
    | [ |- context[eval_dom (dom_meet _ _) _] ] => rewrite eval_dom_meet_iff
    | [ H : context[eval_dom (dom_meet _ _) _] |- _ ] => rewrite eval_dom_meet_iff in H
    (* Finishing hypotheses *)
    | [ H : eval_domset ?D ?T |- eval_dom (?X, (var_dom ?D ?X)) ?T ] =>
      rewrite eval_domset_alt in H; apply H
  (*
    | [ H1 : eval_domset ?S ?X ?D ?Sp, H2 : eval_domset ?Sp ?T |- eval_domset ?S ?T ] =>
      apply (apply_vardom_2l S X D); assumption *)
    | [ H : eval_domset (apply_vardom ?S ?X ?D) ?T |- eval_domset ?D ] =>
      apply (apply_vardom_2r S X D); assumption
    end).

(* Weirdly, omega can't seem to discover the following. *)
Lemma Z_le_le_eq : forall (x y : Z), x <= y -> y <= x -> x = y.
Proof. intros; omega. Qed.
Lemma Z_eq_le : forall (x y : Z), x = y -> x <= y.
Proof. intros; omega. Qed.
Lemma Z_eq_ge : forall (x y : Z), x = y -> y <= x.
Proof. intros; omega. Qed.

Lemma dom_le_spec : forall x k theta, eval_dom (x, dom_le k) theta <-> Z.le (theta x) k.
Proof. unfold eval_dom, sat_dom; dom_simpl; simpl; unfold_satdb; intros; split; tsimpl. now apply zset.notmem_empty in H0. Qed.

Lemma dom_ge_spec : forall x k theta, eval_dom (x, dom_ge k) theta <-> Z.le k (theta x).
Proof. unfold eval_dom, sat_dom; dom_simpl; simpl; unfold_satdb; intros; split; tsimpl. now apply zset.notmem_empty in H0. Qed.

Lemma dom_const_spec : forall x k theta, eval_dom (x, dom_const k) theta <-> Z.eq (theta x) k.
Proof. unfold eval_dom, sat_dom; dom_simpl; simpl; unfold_satdb; intros; split; tsimpl.
       now apply Z_le_le_eq.
       now apply Z_eq_le. now apply Z_eq_ge.
       now apply zset.notmem_empty in H0.
Qed.

Lemma dom_neq_spec : forall x k theta, eval_dom (x, dom_neq k) theta <-> (theta x) <> k.
Proof.
  intros; split; intros; unfold dom_neq, eval_dom, sat_dom, sat_dbound, sat_lb, sat_ub in *; tsimpl.
  assert (Hi := zset.mem_k_addk zset.empty k); congruence.
  apply zset.mem_addk_if in H0.
  destruct H0 ; [congruence | now apply zset.notmem_empty in H0].
Qed.

Lemma dom_range_spec : forall x l u theta, eval_dom (x, dom_range l u) theta <-> l <= (theta x) <= u.
Proof.
  unfold eval_dom, sat_dom; dom_simpl; simpl; unfold_satdb; intros; split; tsimpl. now apply zset.notmem_empty in H1.
Qed.

Lemma eval_dom_sat_equiv : forall x d t, eval_dom (x, d) t <-> sat_dom d (t x).
Proof. now unfold eval_dom. Qed.

Lemma term_dom_valid :
  forall ds theta,
    eval_domset ds theta -> forall t, sat_dom (term_dom ds t) (eval_iterm t theta).
Proof.
  intros. unfold term_dom, eval_iterm; destruct t.
  + apply eval_domset_vardom with (x := i) in H.
    unfold eval_dom in H; simpl in H.
    assumption.
  + unfold sat_dom, dom_const, sat_dbound, sat_lb, sat_ub; simpl.
    split; [omega | apply zset.notmem_empty ].
Qed.

Ltac dom_spec :=
    repeat (
      match goal with
        | [ H : context[eval_dom (?X, dom_const ?K) ?T] |- _ ] => rewrite dom_const_spec in H
        | [ H : context[eval_dom (?X, dom_le ?K) ?T] |- _ ] => rewrite dom_le_spec in H
        | [ H : context[eval_dom (?X, dom_ge ?K) ?T] |- _ ] => rewrite dom_ge_spec in H
        | [ H : context[eval_dom (?X, dom_neq ?K) ?T] |- _ ] => rewrite dom_neq_spec in H
        | [ H : context[sat_dom (dom_const ?K) (?T ?X)] |- _] => (rewrite <- (eval_dom_sat_equiv X (dom_const K) T) in H; rewrite dom_const_spec in H)
        | [ H : context[sat_dom (dom_le ?K) (?T ?X)] |- _] => (rewrite <- (eval_dom_sat_equiv X (dom_le K) T) in H; rewrite dom_le_spec in H)
        | [ H : context[sat_dom (dom_ge ?K) (?T ?X)] |- _] => (rewrite  <- (eval_dom_sat_equiv X (dom_ge K) T) in H; rewrite dom_ge_spec in H)
        | [ H : context[sat_dom (dom_neq ?K) (?T ?X)] |- _] => (rewrite  <- (eval_dom_sat_equiv X (dom_neq K) T) in H; rewrite dom_neq_spec in H)
      end
    ).