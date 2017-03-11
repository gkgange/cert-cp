(* Types & code for proof logs. *)
Require Import ZArith.
Require Import assign.
Require Import domain.
Require Import model.
Require Import resolution.
Require Import Recdef.
Require Import map.
Require Import lit.
Require Import clause_domain.
Module ZMapProperties := FMapFacts.WProperties(ZMaps).

Definition asg := valuation.
Fixpoint amap_with_alist (amap : ZMaps.t Z) asgs :=
  match asgs with
  | nil => amap
  | cons (x, k) asgs' => amap_with_alist (ZMaps.add x k amap) asgs'
  end.

Definition asg_of_alist alist :=
  let amap := amap_with_alist (ZMaps.empty Z) alist in
  (fun x => match ZMaps.find x amap with
     | None => 0%Z
     | Some k => k
     end).

Definition clause_map := zmap clause.
Definition cst_map := zmap cst.
                            
Inductive step :=
  | Intro : Z -> clause -> step
  | Hint : Z -> step
  | Del : Z -> step
  | Resolve : Z -> clause -> list Z -> step.

Definition state := ((zmap cst) * (zmap clause) * Z)%type.

Ltac destate s := destruct s as (p, h) ; destruct p as (cs, cls).
Inductive status :=
  | Unknown
  | Unsat
  | Invalid : step -> status.

Definition eval_cstmap cs theta :=
  forall (id : Z) (c : cst),
    ZMaps.MapsTo id c cs -> eval_cst c theta.

Fixpoint cst_map_of_csts cs :=
  match cs with
  | nil => ZMaps.empty cst
  | cons (k, c) cs' =>
      ZMaps.add k c (cst_map_of_csts cs')
  end.
Lemma cst_map_if_csts : forall (cs : list (Z * cst)) (theta : valuation),
  eval_csts cs theta -> eval_cstmap (cst_map_of_csts cs) theta.
Proof.
  induction cs.

  unfold eval_cstmap, cst_map_of_csts; intros; now apply ZMapProperties.F.empty_mapsto_iff in H0.

  unfold eval_csts, eval_cstmap; fold eval_csts; fold eval_cstmap; destruct a; simpl in *; intros.
  destruct H as [Hc Hcs].
  apply ZMapProperties.F.add_mapsto_iff in H0.
  destruct H0 as [He | Hd]; [destruct He as [Hz Hc0] | destruct Hd as [Hd Hmap]].
    rewrite <- Hc0; assumption.
    apply IHcs in Hcs; unfold eval_cstmap in Hcs; now apply Hcs with (id := id).
Qed.

Fixpoint cst_map_of_csts_acc (m : zmap cst) cs :=
  match cs with
  | nil => m
  | cons (k, c) cs' =>
      cst_map_of_csts_acc (ZMaps.add k c m) cs'
  end.

Lemma cst_map_of_csts_eq : forall xs, cst_map_of_csts xs = cst_map_of_csts_acc (ZMaps.empty _) (List.rev xs).
Proof.
  intros.
  assert (cst_map_of_csts xs = List.fold_right (fun t m => ZMaps.add (fst t) (snd t) m) (ZMaps.empty _) xs).
    induction xs.
    trivial.
    destruct a.
    unfold cst_map_of_csts, List.fold_right; simpl; fold cst_map_of_csts; fold List.fold_right.
    rewrite IHxs.
    trivial.
  assert (forall m ys, cst_map_of_csts_acc m ys = List.fold_left (fun m t => (fun t m => ZMaps.add (fst t) (snd t) m) t m) ys m).
    intros m ys.
    generalize m; clear m; induction ys; intro m.
    trivial.
    destruct a.
    unfold cst_map_of_csts_acc at 1; simpl; fold cst_map_of_csts_acc.
    rewrite IHys.
    trivial.
    rewrite H0.
    rewrite H.
    rewrite <- List.fold_left_rev_right.
    now rewrite List.rev_involutive.
Qed.

Definition state_csts (s : state) :=
  match s with
  | (cs, clauses, hint) => cs
  end.

Definition eval_clauses_alt (cs : list clause) theta :=
  forall cl, List.In cl cs -> eval_clause cl theta.
Lemma eval_clauses_iff : forall cs theta, eval_clauses cs theta <-> eval_clauses_alt cs theta.
Proof.
  induction cs.
  intros; unfold eval_clauses, eval_clauses_alt.
  split; intros;
    [now apply List.in_nil in H0 | trivial].
  unfold eval_clauses, eval_clauses_alt; fold eval_clauses; fold eval_clauses_alt.
  split; intros.
    destruct H as [Ha Hcs].
    apply List.in_inv in H0.
    destruct H0 as [H0 | H0];
      [now rewrite <- H0 | apply IHcs in Hcs; unfold eval_clauses_alt in Hcs; now apply Hcs].

    split; [apply H; apply List.in_eq |
            apply IHcs; unfold eval_clauses_alt; intros; apply H; now apply List.in_cons].
Qed.

Definition eval_clmap clauses theta :=
  forall id cl, ZMaps.MapsTo id cl clauses -> eval_clause cl theta.

Definition inference_valid (s : state) (cl : clause) :=
  match s with
  | (cs, clauses, old) => forall theta,
      eval_cstmap cs theta -> eval_clause cl theta
  end.

Definition inference_valid_bnd (bs : domset) (s : state) (cl : clause) :=
  match s with
  | (cs, clauses, old) => forall theta,
      eval_domset bs theta -> eval_cstmap cs theta -> eval_clause cl theta
  end.

Definition state_valid (s : state) :=
  match s with
  | (cs, clauses, old) => forall (id : Z) (cl : clause),
      ZMaps.MapsTo id cl clauses -> forall theta,
        eval_cstmap cs theta -> eval_clause cl theta
  end.
  
Definition state_valid_bnd (bs : domset) (s : state) :=
  match s with
  | (cs, clauses, old) =>
    forall (id : Z) (cl : clause),
      ZMaps.MapsTo id cl clauses -> forall theta,
        eval_domset bs theta ->
        eval_cstmap cs theta -> eval_clause cl theta
  end.
  
Definition empty_state (m : model) :=
  match m with
  | (bs, cs) => (cst_map_of_csts_acc (ZMaps.empty _) (List.rev cs), ZMaps.empty clause, (-1))
  end.

Lemma empty_state_valid : forall m, state_valid (empty_state m).
Proof.
  unfold state_valid, empty_state; intros; destruct m; simpl in *.
  intros.
  now apply ZMapProperties.F.empty_mapsto_iff in H.  
Qed.

Lemma empty_state_valid_bnd : forall m bs, state_valid_bnd bs (empty_state m).
Proof.
  intros.
  assert (He := empty_state_valid m).
  unfold state_valid, state_valid_bnd, empty_state in *; intros; destruct m; simpl in *; intros.
  assert (Hm := He id cl).
  apply Hm with (theta := theta); assumption.
Qed.

Definition clause_map_add (cs : clause_map) (id : Z) (cl : clause) := ZMaps.add id cl cs.

Definition clause_map_del (cs : clause_map) (id : Z) := ZMaps.remove id cs.

Lemma clause_map_1 : forall cs cl id theta,
  eval_clmap cs theta -> eval_clause cl theta -> eval_clmap (clause_map_add cs id cl) theta.
Proof.
  unfold eval_clmap, clause_map_add; intros.
  apply ZMapProperties.F.add_mapsto_iff in H1; destruct H1 as [Heq | Hneq];
    [ destruct Heq as [Hid Hcl]; now rewrite <- Hcl
    | destruct Hneq as [Hid Hmap] ; now apply H with (id := id0) ].
Qed.

Lemma clause_map_2 : forall cs id theta,
  eval_clmap cs theta -> eval_clmap (clause_map_del cs id) theta.
Proof.
  unfold eval_clmap, clause_map_del; intros.
  apply ZMaps.remove_3 in H0; now apply H with (id := id0).
Qed.

Definition check_tauto (bs : domset) (cl : clause) :=
  match domset_with_prod bs (negclause cl) with
  | None => true
  | _ => false
  end.
Lemma check_tauto_valid : forall ds cl, check_tauto ds cl = true -> forall theta, eval_domset ds theta -> eval_clause cl theta.
Proof.
  intros ds cl; unfold check_tauto.
  eqelim (domset_with_prod ds (negclause cl)); [discriminate | trivial].
  intros; clear H.
  apply eval_clause_notprod; intro.
  assert (eval_domset (domset_with_prod ds (negclause cl)) theta).
    apply domset_with_prod_iff; tauto.
    now rewrite H0 in H2.
Qed.

Definition check_inf bs cst cl :=
  let ds := domset_with_prod bs (negclause cl) in
  match ds with
    | None => true
    | Some _ => check_cst_unsat cst ds
  end.

Lemma check_inf_valid : forall bs cst cl, check_inf bs cst cl = true ->
  forall theta, eval_domset bs theta -> eval_cst cst theta -> eval_clause cl theta.
Proof.
  intros bs cst cl; unfold check_inf; intros.
  eqelim (domset_with_prod bs (negclause cl)).
  apply eval_clause_notprod; intro.
  apply check_cst_unsat_valid with (theta := theta) in H.
    contradiction.
    rewrite <- H3; apply domset_with_prod_iff; tauto.
    assumption.
    apply eval_clause_notprod.
    intro.
    assert (H' := domset_with_prod_iff (negclause cl) bs theta); intuition.
    rewrite H3 in *.
    unfold eval_domset in H6; contradiction.
Qed.

Definition check_inference (bs : domset) (s : state) (cl : clause) :=
  match s with
  | (csts, clauses, hint) =>
    match ZMaps.find hint csts with
    | None => check_tauto bs cl
    | Some cst => check_inf bs cst cl
    end
  end.

Lemma check_inference_valid_2 : forall (bs : domset) (s : state) (cl : clause),
  check_inference bs s cl = true -> forall theta, eval_domset bs theta -> eval_cstmap (state_csts s) theta -> eval_clause cl theta.
Proof.
  unfold check_inference; destate s; unfold eval_cstmap; intros.
  remember (ZMaps.find h cs) as fh; destruct fh; simpl in *.
    symmetry in Heqfh; apply find_mapsto_iff in Heqfh.
    apply check_inf_valid with (bs := bs) (cst := c). assumption. assumption. now apply H1 with (id := h).
    now apply check_tauto_valid with (ds := bs).
Qed.

Lemma check_inference_valid : forall (bs : domset) (s : state) (cl : clause),
   check_inference bs s cl = true -> inference_valid_bnd bs s cl.
Proof.
  intros.
  unfold inference_valid_bnd; intros; destate s; intros.
  now apply check_inference_valid_2 with (bs := bs) (s := ((cs, cls), h)) (theta := theta).
Qed.
  
Definition set_hint (s : state) (hint : Z) : state:=
  match s with
  | (csts, clauses, old) => (csts, clauses, hint)
  end.
Lemma set_hint_valid : forall (bs : domset) (s : state) (hint : Z),
  state_valid_bnd bs s -> state_valid_bnd bs (set_hint s hint).
Proof.
  unfold state_valid_bnd, set_hint; destate s; simpl; intros.
  now apply H with (id := id).
Qed.

Definition del_clause (s : state) cid :=
  match s with
  | (cs, clauses, hint) => (cs, ZMaps.remove cid clauses, hint)
  end.
Lemma del_clause_valid : forall bs s id, state_valid_bnd bs s -> state_valid_bnd bs (del_clause s id).
Proof.
  unfold del_clause, state_valid_bnd; destate s; simpl; intros.
  apply ZMaps.remove_3 in H0.
  now apply H with (id := id0) (cl := cl) (theta := theta) in H0.
Qed.

Definition add_clause (s : state) cid cl :=
  match s with
  | (cs, clauses, hint) => (cs, ZMaps.add cid cl clauses, hint)
  end.
Theorem add_clause_valid : forall (bs : domset) (s : state) (id : Z) (cl : clause),
  state_valid_bnd bs s -> inference_valid_bnd bs s cl -> state_valid_bnd bs (add_clause s id cl).
Proof.
  unfold state_valid_bnd, inference_valid_bnd, add_clause;
  destate s; simpl; intros.
  apply ZMapProperties.F.add_mapsto_iff in H1.
  destruct H1 as [Heq | Hdis].
  destruct Heq as [Hid Hcl]; rewrite <- Hcl; now apply H0.
  destruct Hdis as [Hid Hmap].
  now  apply H with (id := id0) (cl := cl0) (theta := theta).
Qed.

Definition apply_inference (bs : domset) (s : state) (id : Z) (cl : clause) :=
  if check_inference bs s cl then
    add_clause s id cl
  else
    s.
Lemma apply_inference_valid : forall bs s id cl,
  state_valid_bnd bs s -> state_valid_bnd bs (apply_inference bs s id cl).
Proof.
  unfold apply_inference; simpl; intros.
  remember (check_inference bs s cl) as c; symmetry in Heqc; destruct c.
  apply add_clause_valid.
    assumption.
    now apply check_inference_valid. assumption.
Qed.

Fixpoint clauses_deref (cs : clause_map) (ids : list Z) :=
  match ids with
  | nil => nil
  | cons id ids' =>
      let rest := clauses_deref cs ids' in
      match ZMaps.find id cs with
      | None => rest
      | Some cl => cons cl rest
      end
  end.

  
Theorem clauses_deref_1 : forall cs ids theta,
  eval_clmap cs theta -> eval_clauses (clauses_deref cs ids) theta.
Proof.
  intros cs ids theta;
  rewrite eval_clauses_iff; unfold eval_clmap, eval_clauses_alt; intros; induction ids.
  unfold clauses_deref in *; now apply List.in_nil in H0.
  unfold clauses_deref in H0; fold clauses_deref in H0.
  remember (ZMaps.find a cs) as fa.
  destruct fa; simpl in *.
  destruct H0 as [Heq | Hin] ;
    [rewrite <- Heq; symmetry in Heqfa; apply H with (id := a); now apply find_mapsto_iff | apply IHids ; now apply Hin].
  now apply IHids.
Qed.

Definition get_clauses (s : state) (ids : list Z) :=
  match s with
  | (cs, cls, h) => clauses_deref cls ids
  end.

Definition apply_resolution (s : state) (id : Z) (cl : clause) (ants : list Z) :=
  if resolvable cl (get_clauses s ants) then
    (* add_clause s id (simplify_clause cl) *)
    add_clause s id cl
  else
    s.
Lemma apply_resolution_valid : forall (bs : domset) (s : state) (id : Z) (cl : clause) (ants : list Z),
  state_valid_bnd bs s -> state_valid_bnd bs (apply_resolution s id cl ants).
Proof.
  intros; unfold apply_resolution.
  remember (resolvable cl (get_clauses s ants)) as r; symmetry in Heqr; destruct r; simpl in *;
    try assumption.
  remember (get_clauses s ants) as acl.
  apply add_clause_valid; try assumption.
  unfold inference_valid_bnd; destate s; intros.
  apply resolvable_valid with (theta := theta) (ants := acl).
    assumption.
    rewrite Heqacl; unfold get_clauses.
    apply clauses_deref_1.
    unfold state_valid in H.
    unfold eval_clmap; intros; apply H with (id := id0); assumption.
Qed.

Definition apply_step (bs : domset) (s : state) (d : step) :=
  match d with
  | Intro cid cl => apply_inference bs s cid cl
  | Hint cid => set_hint s cid
  | Del cid => del_clause s cid
  | Resolve cid cl ants => apply_resolution s cid cl ants
   end.
Theorem apply_step_valid : forall (bs : domset) (s : state) (d : step),
  state_valid_bnd bs s -> state_valid_bnd bs (apply_step bs s d).
Proof.
  intros; unfold apply_step; destruct d; simpl in *.
    now apply apply_inference_valid.
    now apply set_hint_valid.
    now apply del_clause_valid.
    now apply apply_resolution_valid.
Qed.

Fixpoint apply_step_list (bs : domset) (s : state) (ds : list step) :=
  match ds with
  | nil => s
  | cons d ds' => apply_step_list bs (apply_step bs s d) ds'
  end.
       
Theorem apply_step_list_valid : forall (bs : domset) (ds : list step) (s : state),
  state_valid_bnd bs s -> state_valid_bnd bs (apply_step_list bs s ds).
Proof.
  induction ds.
    intros; now unfold apply_step_list.

    unfold apply_step_list; fold apply_step_list. 
    intros; apply IHds.
    now apply apply_step_valid.
Qed.

CoInductive steps :=
  | Fin : steps
  | Steps : step -> steps -> steps.

Function apply_steps (bs : domset) (s : state) (lim : Z) (ds : steps) { measure Zabs_nat lim } :=
  if Z.leb lim (0%Z) then
    s 
  else
    match ds with
    | Fin => s
    | Steps d ds' =>
       apply_steps bs (apply_step bs s d) (Zpred lim) ds'
    end.
  intros.
  apply Z.leb_nle in teq.
  apply Zabs_nat_lt; omega.
Defined.

Function apply_steps_gen (bs : domset) (s : state) (lim : Z) (T : Type) (x : T) (next : T -> option (step * T))
         { measure Zabs_nat lim } :=
  if Z.leb lim (0%Z) then
    s
  else match next x with
    | None => s
    | Some (d, x') => apply_steps_gen bs (apply_step bs s d) (Zpred lim) T x' next
  end.
  intros.    
  apply Z.leb_nle in teq.
  apply Zabs_nat_lt; omega.
Defined.

Definition apply_steps_validP (bs : domset) s (lim : Z) (ds : steps) s' :=
  state_valid_bnd bs s -> state_valid_bnd bs s'.

Theorem apply_steps_valid : forall (bs : domset) (s : state) (lim : Z) (ds : steps),
  state_valid_bnd bs s -> state_valid_bnd bs (apply_steps bs s lim ds).
Proof.
  intro bs.
  assert (Hi := apply_steps_ind bs (apply_steps_validP bs)).
  unfold apply_steps_validP in *.
  intros; apply Hi.
    trivial.
    trivial.

    intros.
    apply H0.    
    now apply apply_step_valid.
    assumption.
Qed.

Theorem apply_steps_gen_valid : forall bs s lim T x next,
  state_valid_bnd bs s -> state_valid_bnd bs (apply_steps_gen bs s lim T x next).
Proof.
  intros bs s lim T x next.
  apply apply_steps_gen_ind; intros; try congruence.
  apply H. apply apply_step_valid; assumption.
Qed.

Fixpoint contains_false (cs : list (Z * clause)) :=
  match cs with
  | nil => false
  | cons (_, c) cs' =>
    match c with
    | nil => true
    | _ => contains_false cs'
    end
  end.

Lemma contains_false_1 : forall cs, contains_false cs = true -> exists k, List.In (k, nil) cs.
Proof.
  induction cs.
    unfold contains_false; discriminate.

    unfold contains_false; fold contains_false.
    destruct a; destruct c; simpl in *; intros.
      exists z; now left.

    apply IHcs in H.
    elim H.
    intros.
    exists x.
    now right.
Qed.

Lemma contains_false_unsat : forall (cs : clause_map),
  contains_false (ZMaps.elements cs) = true -> forall theta, ~ eval_clmap cs theta.
Proof.
  intros.
  apply contains_false_1 in H.
  intro Hcs.
  unfold eval_clmap in Hcs.
  elim H; intros.
  assert (eval_clause nil theta).
  apply Hcs with (id := x).
  rewrite ZMapProperties.F.elements_mapsto_iff.
  apply SetoidList.In_InA with (eqA := ZMaps.eq_key_elt (elt := clause)) in H0; try assumption.
  apply ZMapProperties.eqke_equiv.
  now unfold eval_clause in H1.
Qed.

Definition state_unsat (s : state) :=
  match s with
  | (_, cs, _) => contains_false (ZMaps.elements cs)
  end.

Lemma state_unsat_valid : forall bs s, state_unsat s = true -> state_valid_bnd bs s -> forall theta, eval_domset bs theta -> ~ eval_cstmap (state_csts s) theta.
Proof.
  intros bs s.
  unfold state_unsat, state_valid.
  destruct s; destruct p; simpl.
  intros.
  intro; unfold eval_cstmap.
  apply contains_false_1 in H.
  elim H; intros.
  apply SetoidList.In_InA with (eqA := ZMaps.eq_key_elt (elt := clause)) in H3.
  apply ZMapProperties.F.elements_mapsto_iff in H3.
  apply H0 with (theta := theta) in H3.
  now unfold eval_clause in H3.
  assumption.
  assumption. apply ZMapProperties.eqke_equiv.
Qed.

Lemma state_csts_const : forall bs s lim ss, state_csts s = state_csts (apply_steps bs s lim ss).
Proof.
  intro bs.
  set (I s (_ : Z) (_ : steps) s' := state_csts s = state_csts s').
  apply (apply_steps_ind bs I); unfold I; clear I; intros;
    unfold state_csts in *; destruct s; destruct p; simpl in *; try congruence.
  rewrite <- H.  
  unfold apply_step; try unfold apply_inference; simpl; try congruence.
  destruct d; simpl; try congruence.
  destruct (ZMaps.find (elt := cst) z z0); simpl; try congruence.
  destruct (check_inf bs c0 c); try congruence.
  destruct (check_tauto bs c); try congruence.
  unfold apply_resolution.
    destruct (resolvable c (get_clauses (z0, z1, z) l));
      unfold add_clause; try congruence.
Qed.

Lemma state_csts_const_gen : forall bs s lim T x next, state_csts s = state_csts (apply_steps_gen bs s lim T x next).
Proof.
  intros bs s lim T x next.
  apply (apply_steps_gen_ind bs); intros; try assumption; try congruence.
  rewrite <- H.
  clear H.
  unfold state_csts in *; destruct s0; destruct p; simpl in *; try congruence.
  unfold apply_step; try unfold apply_inference; simpl; try congruence.
  destruct d; simpl; try congruence.
  destruct (ZMaps.find (elt := cst) z z0); simpl; try congruence.
  destruct (check_inf bs c0 c); try congruence.
  destruct (check_tauto bs c); try congruence.
  unfold apply_resolution;
    destruct (resolvable c (get_clauses (z0, z1, z) l));
      unfold add_clause; try congruence.
Qed.
  
Definition certify_unsat_stream (m : model) (lim : Z) (s : steps) :=
  state_unsat (apply_steps (domset_of_bounds (fst m)) (empty_state m) lim s). 

Theorem certify_unsat_stream_valid : forall m lim s,
  certify_unsat_stream m lim s = true -> model_unsat m.
Proof.
  intros m lim s.
  unfold certify_unsat_stream, model_unsat.
  intros.
  remember (domset_of_bounds (fst m)) as bs.
  assert (Hs0 := empty_state_valid_bnd m bs).
  apply (apply_steps_valid bs (empty_state m) lim s) in Hs0.
  intros Hem.
  destruct m.
  unfold eval_model in Hem; destruct Hem as [Hb Hcs].
  apply state_unsat_valid with (bs := bs) (theta := theta) in H.
  rewrite <- state_csts_const in H.
  clear Hs0.
  unfold empty_state, state_csts in *; simpl in *.
  apply cst_map_if_csts in Hcs.
  rewrite cst_map_of_csts_eq in Hcs.
  contradiction.
  assumption.
  apply domset_of_bounds_valid in Hb.
  rewrite Heqbs.
  assumption.
Qed.

Definition certify_unsat (m : model) (lim : Z) (T : Type) (x : T) (next : T -> option (step * T)) :=
  state_unsat (apply_steps_gen (domset_of_bounds (fst m)) (empty_state m) lim T x next). 

Theorem certify_unsat_valid : forall m lim T x next,
  certify_unsat m lim T x next = true -> model_unsat m.                                
Proof.
  intros m lim T x next.
  unfold certify_unsat, model_unsat.
  intros.
  remember (domset_of_bounds (fst m) ) as bs.
  assert (Hs0 := empty_state_valid_bnd m).
  apply (apply_steps_gen_valid bs (empty_state m) lim T x next) in Hs0.
  intros Hem.
  destruct m; unfold eval_model in Hem; destruct Hem as [Hb Hcs].
  apply state_unsat_valid with (bs := bs) (theta := theta) in H.
  rewrite <- state_csts_const_gen in H.
  clear Hs0.
  unfold empty_state, state_csts in *; simpl in *.
  apply cst_map_if_csts in Hcs.
  rewrite cst_map_of_csts_eq in Hcs.
  contradiction.
  assumption.
  apply domset_of_bounds_valid in Hb.
  now rewrite Heqbs.
Qed.

Definition certify_unsat_list (m : model) (ss : list step) :=
  certify_unsat m (Z_of_nat (List.length ss)) (list step) ss
    (fun ss =>
       match ss with
       | nil => None
       | cons s ss' => Some (s, ss')
       end).
Corollary certify_unsat_list_valid : forall m ss,
  certify_unsat_list m ss = true -> model_unsat m.
Proof.
  intros m ss; unfold certify_unsat_list; apply certify_unsat_valid.
Qed.

Definition check_inference_domset (ds : domset) (cs : cst_map) (hint : Z) (cl : clause) :=
  match ZMaps.find hint cs with
  | None => check_tauto ds cl
  | Some cst => check_inf ds cst cl
  end.

Lemma check_inference_domset_valid : forall ds cs hint cl,
  check_inference_domset ds cs hint cl = true -> forall theta,
    eval_domset ds theta -> eval_cstmap cs theta -> eval_clause cl theta.
Proof.
  unfold check_inference_domset; intros.
  eqelim (ZMaps.find hint cs); zmap_simpl.
  unfold eval_cstmap in H1; specialize (H1 hint c).
  apply check_inf_valid with (bs := ds) (cst := c); tauto.
  apply check_tauto_valid with (ds := ds); tauto.
Qed.

(*
Lemma eval_domset_if_bounds : forall bs theta,
  eval_bounds bs theta -> eval_domset (bounds_domset bs) theta.
Proof.
  intros.
  unfold bounds_domset.
  rewrite negclause_of_bounds_valid in H.
  now apply eval_negcl_domset in H.
Qed.
*)

(*
Lemma eval_bounds_if_domset : forall bs theta,
  eval_domset (bounds_domset bs) theta -> eval_bounds bs theta.
Proof.
  intros.
  unfold bounds_domset in H.
  rewrite negclause_of_bounds_valid.
*)

(* Check a single inference for a model. *)
Definition check_inference_model m hint cl :=
  let s0 := empty_state m in
  let sH := set_hint s0 hint in
  check_inference (domset_of_bounds (fst m)) sH cl.
Lemma check_inference_model_valid : forall m hint cl,
  check_inference_model m hint cl = true -> forall theta, eval_model m theta -> eval_clause cl theta.
Proof.
  intros m hint cl.
  unfold check_inference_model.
  intro.
  apply (check_inference_valid (domset_of_bounds (fst m)) (set_hint (empty_state m) hint) cl) in H.
  assert (Hv := empty_state_valid_bnd m (domset_of_bounds (fst m))).
  intros.
  unfold eval_model in H0; destruct m; destruct H0 as [Hb Hc].
  unfold empty_state, set_hint in *; simpl in *.
  apply H; try assumption.
  apply domset_of_bounds_valid; assumption.
  rewrite <- cst_map_of_csts_eq.
  now apply cst_map_if_csts.
Qed.

Definition certify_solution m sol := check_model_sol m sol.

Theorem certify_solution_valid : forall m sol, certify_solution m sol = true -> eval_model m sol.
Proof.
  intros; now apply check_model_sol_valid.
Qed.

Definition domset_with_lt ds x k := apply_vardom ds x (dom_le (k-1)).
Lemma domset_with_lt_iff : forall ds x k theta, eval_domset ds theta /\ (theta x < k) <-> eval_domset (domset_with_lt ds x k) theta.
Proof.
  intros; unfold domset_with_lt; tsimpl.
  apply apply_vardom_1; [exact H | apply dom_le_spec; omega].
  now apply apply_vardom_2l with (x := x) (d := (dom_le (k-1))).
  apply apply_vardom_2r in H.
  apply dom_le_spec in H; omega.
Qed.

Definition certify_optimal (m : model) (obj : ivar) (sol : valuation) (lim : Z) (T : Type) (x : T) (next : T -> option (step * T)) :=
  let b0 := domset_of_bounds (fst m) in
  let bs := domset_with_lt b0 obj (sol obj) in
  andb (certify_solution m sol) (state_unsat (apply_steps_gen bs (empty_state m) lim T x next)).

Theorem certify_optimal_valid : forall m obj sol lim T x next,
  certify_optimal m obj sol lim T x next = true -> is_model_minimum m obj sol.
Proof.
  unfold certify_optimal, is_model_minimum, is_model_ub; intros.
  rewrite Bool.andb_true_iff in H.
  destruct H as [Hs Hp].
  split; [now apply certify_solution_valid | trivial].

  intros sol' H.
  remember (domset_of_bounds (fst m)) as b0.
  remember (domset_with_lt b0 obj (sol obj)) as bs.
  assert (Hs0 := empty_state_valid_bnd m bs).
  remember (empty_state m) as s0.
  apply apply_steps_gen_valid with (lim := lim) (x := x) (next := next) in Hs0.
  assert (Hsc := state_csts_const_gen bs s0 lim T x next).
  remember (apply_steps_gen bs s0 lim T x next) as sF.
  assert (eval_domset bs sol' -> ~ eval_cstmap (state_csts sF) sol').
    intros.
    apply state_unsat_valid with (bs := bs); try assumption.

  unfold eval_model in H; destruct m; destruct H as [Hb Hcs].
  assert (sol obj <= sol' obj \/ sol' obj < sol obj).
    omega.
  destruct H ; [assumption | trivial].
  assert (eval_domset bs sol').
    rewrite Heqbs.
    apply domset_with_lt_iff.
    apply domset_of_bounds_valid in Hb.
    split.
    now rewrite Heqb0.
    omega.

  apply H0 in H1.  
  apply cst_map_if_csts in Hcs.
  rewrite <- Hsc in H1.
  rewrite Heqs0 in H1.
  unfold empty_state, state_csts in H1; simpl in *.
  rewrite <- cst_map_of_csts_eq in H1.
  contradiction.
Qed.
Definition certify_optimal_list m obj sol p_proof :=
  certify_optimal m obj sol
                  (Z.of_nat (List.length p_proof))
                  _
                  p_proof
                  (fun p =>
                     match p with
                       | nil => None
                       | cons s p' => Some (s, p')
                     end).
Corollary certify_optimal_list_valid : forall m obj sol p_proof,
  certify_optimal_list m obj sol p_proof = true -> is_model_minimum m obj sol.
Proof.
  unfold certify_optimal_list; intros m obj sol p_proof; apply certify_optimal_valid.
Qed.