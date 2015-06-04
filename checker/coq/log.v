(* Types & code for proof logs. *)
Require Import ZArith.
Require Import prim.
Require Import sol.
Require Import bounds.
Require Import domain.
Require Import model.
Require Import map.
Require Import resolution.
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

Definition state_csts (s : state) :=
  match s with
  | (cs, clauses, hint) => cs
  end.

Definition eval_clauses (cs : list clause) theta :=
  forall cl, List.In cl cs -> eval_clause cl theta.

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
  unfold eval_clmap, eval_clauses; intros; induction ids.
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
  now apply resolvable_valid with (theta := theta) (ants := acl).
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