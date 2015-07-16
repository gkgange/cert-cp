(* Types & code for proof logs. *)
Require Import ZArith.
Require Import prim.
Require Import sol.
Require Import bounds.
Require Import domain.
Require Import model.
Require Import map.
Require Import resolution.
Require Import Recdef.
Module ZMapProperties := FMapFacts.WProperties(ZMaps).

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
Lemma cst_map_if_csts : forall (cs : list (Z * cst)) (theta : asg),
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

Definition state_valid (s : state) :=
  match s with
  | (cs, clauses, old) => forall (id : Z) (cl : clause),
      ZMaps.MapsTo id cl clauses -> forall theta,
        eval_cstmap cs theta -> eval_clause cl theta
  end.
  
Definition empty_state (m : model) :=
  match m with
  | (bs, cs) => (cst_map_of_csts cs, ZMaps.empty clause, (-1))
  end.

Lemma empty_state_valid : forall m, state_valid (empty_state m).
Proof.
  unfold state_valid, empty_state; intros; destruct m; simpl in *.
  intros.
  now apply ZMapProperties.F.empty_mapsto_iff in H.  
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

Definition check_inference (s : state) (cl : clause) :=
  match s with
  | (csts, clauses, hint) =>
    match ZMaps.find hint csts with
    | None => false
    | Some cst => check_cst cst cl
    end
  end.

Lemma check_inference_valid_2 : forall (s : state) (cl : clause),
  check_inference s cl = true -> forall theta, eval_cstmap (state_csts s) theta -> eval_clause cl theta.
Proof.
  unfold check_inference; destate s; unfold eval_cstmap; intros.
  remember (ZMaps.find h cs) as fh; destruct fh; simpl in *.
    symmetry in Heqfh; apply find_mapsto_iff in Heqfh.
    apply check_cst_valid with (c := c). assumption. now apply H0 with (id := h).
    discriminate.
Qed.

Lemma check_inference_valid : forall (s : state) (cl : clause),
   check_inference s cl = true -> inference_valid s cl.
Proof.
  intros.
  unfold inference_valid; intros; destate s; intros.
  now apply check_inference_valid_2 with (s := ((cs, cls), h)) (theta := theta).
Qed.
  
Definition set_hint (s : state) (hint : Z) : state:=
  match s with
  | (csts, clauses, old) => (csts, clauses, hint)
  end.
Lemma set_hint_valid : forall (s : state) (hint : Z),
  state_valid s -> state_valid (set_hint s hint).
Proof.
  unfold state_valid, set_hint; destate s; simpl; intros.
  now apply H with (id := id).
Qed.

Definition del_clause (s : state) cid :=
  match s with
  | (cs, clauses, hint) => (cs, ZMaps.remove cid clauses, hint)
  end.
Lemma del_clause_valid : forall s id, state_valid s -> state_valid (del_clause s id).
Proof.
  unfold del_clause, state_valid; destate s; simpl; intros.
  apply ZMaps.remove_3 in H0.
  now apply H with (id := id0) (cl := cl) (theta := theta) in H0.
Qed.

Definition add_clause (s : state) cid cl :=
  match s with
  | (cs, clauses, hint) => (cs, ZMaps.add cid cl clauses, hint)
  end.
Theorem add_clause_valid : forall (s : state) (id : Z) (cl : clause),
  state_valid s -> inference_valid s cl -> state_valid (add_clause s id cl).
Proof.
  unfold state_valid, inference_valid, add_clause;
  destate s; simpl; intros.
  apply ZMapProperties.F.add_mapsto_iff in H1.
  destruct H1 as [Heq | Hdis].
  destruct Heq as [Hid Hcl]; rewrite <- Hcl; now apply H0.
  destruct Hdis as [Hid Hmap].
  now  apply H with (id := id0) (cl := cl0) (theta := theta).
Qed.

Definition apply_inference (s : state) (id : Z) (cl : clause) :=
  if check_inference s cl then
    add_clause s id cl
  else
    s.
Lemma apply_inference_valid : forall s id cl,
  state_valid s -> state_valid (apply_inference s id cl).
Proof.
  unfold apply_inference; simpl; intros.
  remember (check_inference s cl) as c; symmetry in Heqc; destruct c.
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
    add_clause s id cl
  else
    s.
Lemma apply_resolution_valid : forall (s : state) (id : Z) (cl : clause) (ants : list Z),
  state_valid s -> state_valid (apply_resolution s id cl ants).
Proof.
  intros; unfold apply_resolution.
  remember (resolvable cl (get_clauses s ants)) as r; symmetry in Heqr; destruct r; simpl in *;
    try assumption.
  remember (get_clauses s ants) as acl.
  apply add_clause_valid; try assumption.
  unfold inference_valid; destate s; intros.
  apply resolvable_valid with (theta := theta) (ants := acl).
    assumption.
    rewrite Heqacl; unfold get_clauses.
    apply clauses_deref_1.
    unfold state_valid in H.
    unfold eval_clmap; intros; apply H with (id := id0); assumption.
Qed.

Definition apply_step (s : state) (d : step) :=
  match d with
  | Intro cid cl => apply_inference s cid cl
  | Hint cid => set_hint s cid
  | Del cid => del_clause s cid
  | Resolve cid cl ants => apply_resolution s cid cl ants
   end.
Theorem apply_step_valid : forall (s : state) (d : step),
  state_valid s -> state_valid (apply_step s d).
Proof.
  intros; unfold apply_step; destruct d; simpl in *.
    now apply apply_inference_valid.
    now apply set_hint_valid.
    now apply del_clause_valid.
    now apply apply_resolution_valid.
Qed.

Fixpoint apply_step_list (s : state) (ds : list step) :=
  match ds with
  | nil => s
  | cons d ds' => apply_step_list (apply_step s d) ds'
  end.
       
Theorem apply_step_list_valid : forall (ds : list step) (s : state),
  state_valid s -> state_valid (apply_step_list s ds).
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

Function apply_steps (s : state) (lim : Z) (ds : steps) { measure Zabs_nat lim } :=
  if Z_leb lim (0%Z) then
    s 
  else
    match ds with
    | Fin => s
    | Steps d ds' =>
       apply_steps (apply_step s d) (Zpred lim) ds'
    end.
  intros.
  apply Z_leb_false_iff_notle in teq.
  apply Zabs_nat_lt; omega.
Defined.

Function apply_steps_gen (s : state) (lim : Z) (T : Type) (x : T) (next : T -> option (step * T))
         { measure Zabs_nat lim } :=
  if Z_leb lim (0%Z) then
    s
  else match next x with
    | None => s
    | Some (d, x') => apply_steps_gen (apply_step s d) (Zpred lim) T x' next
  end.
  intros.    
  apply Z_leb_false_iff_notle in teq.
  apply Zabs_nat_lt; omega.
Defined.

Definition apply_steps_validP s (lim : Z) (ds : steps) s' :=
  state_valid s -> state_valid s'.

Theorem apply_steps_valid : forall (s : state) (lim : Z) (ds : steps),
  state_valid s -> state_valid (apply_steps s lim ds).
Proof.
  assert (Hi := apply_steps_ind apply_steps_validP).
  unfold apply_steps_validP in *.
  intros; apply Hi.
    trivial.
    trivial.

    intros.
    apply H0.    
    now apply apply_step_valid.
    assumption.
Qed.

Theorem apply_steps_gen_valid : forall s lim T x next,
  state_valid s -> state_valid (apply_steps_gen s lim T x next).
Proof.
  intros s lim T x next.
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

Lemma state_unsat_valid : forall s, state_unsat s = true -> state_valid s -> forall theta, ~ eval_cstmap (state_csts s) theta.
Proof.
  intros s.
  unfold state_unsat, state_valid.
  destruct s; destruct p; simpl.
  intros.
  intro; unfold eval_cstmap.
  apply contains_false_1 in H.
  elim H; intros.
  apply SetoidList.In_InA with (eqA := ZMaps.eq_key_elt (elt := clause)) in H2.
  apply ZMapProperties.F.elements_mapsto_iff in H2.
  apply H0 with (theta := theta) in H2.
  now unfold eval_clause in H2.
  assumption.
  apply ZMapProperties.eqke_equiv.
Qed.

Lemma state_csts_const : forall s lim ss, state_csts s = state_csts (apply_steps s lim ss).
Proof.
  set (I s (_ : Z) (_ : steps) s' := state_csts s = state_csts s').
  apply apply_steps_ind with (P := I); unfold I; clear I; intros;
    unfold state_csts in *; destruct s; destruct p; simpl in *; try congruence.
  rewrite <- H.  
  unfold apply_step; try unfold apply_inference; simpl; try congruence.
  destruct d; simpl; try congruence.
  destruct (ZMaps.find (elt := cst) z z0); simpl; try congruence.
  destruct (check_cst c0 c); try congruence.
  unfold apply_resolution.
    destruct (resolvable c (get_clauses (z0, z1, z) l));
      unfold add_clause; try congruence.
Qed.

 Lemma state_csts_const_gen : forall s lim T x next, state_csts s = state_csts (apply_steps_gen s lim T x next).
Proof.
  intros s lim T x next.
  apply apply_steps_gen_ind; intros; try assumption; try congruence.
  rewrite <- H.
  clear H.
  unfold state_csts in *; destruct s0; destruct p; simpl in *; try congruence.
  unfold apply_step; try unfold apply_inference; simpl; try congruence.
  destruct d; simpl; try congruence.
  destruct (ZMaps.find (elt := cst) z z0); simpl; try congruence.
  destruct (check_cst c0 c); try congruence.
  unfold apply_resolution;
    destruct (resolvable c (get_clauses (z0, z1, z) l));
      unfold add_clause; try congruence.
Qed.
  
Definition certify_unsat_stream (m : model) (lim : Z) (s : steps) :=
  state_unsat (apply_steps (empty_state m) lim s). 

Theorem certify_unsat_stream_valid : forall m lim s,
  certify_unsat_stream m lim s = true -> model_unsat m.
Proof.
  intros m lim s.
  unfold certify_unsat_stream, model_unsat.
  intros.
  assert (Hs0 := empty_state_valid m).
  apply (apply_steps_valid (empty_state m) lim s) in Hs0.
  intros Hem.
  unfold eval_model in Hem; destruct Hem as [Hb Hcs].
  apply state_unsat_valid with (theta := theta) in H.
  rewrite <- state_csts_const in H.
  clear Hs0.
  destruct m; unfold empty_state, state_csts in *; simpl in *.
  apply cst_map_if_csts in Hcs.
  contradiction.
  assumption.
Qed.

Definition certify_unsat (m : model) (lim : Z) (T : Type) (x : T) (next : T -> option (step * T)) :=
  state_unsat (apply_steps_gen (empty_state m) lim T x next). 

Theorem certify_unsat_valid : forall m lim T x next,
  certify_unsat m lim T x next = true -> model_unsat m.                                
Proof.
  intros m lim T x next.
  unfold certify_unsat, model_unsat.
  intros.
  assert (Hs0 := empty_state_valid m).
  apply (apply_steps_gen_valid (empty_state m) lim T x next) in Hs0.
  intros Hem.
  unfold eval_model in Hem; destruct Hem as [Hb Hcs].
  apply state_unsat_valid with (theta := theta) in H.
  rewrite <- state_csts_const_gen in H.
  clear Hs0.
  destruct m; unfold empty_state, state_csts in *; simpl in *.
  apply cst_map_if_csts in Hcs.
  contradiction.
  assumption.
Qed.
