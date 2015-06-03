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
  | Valid
  | Invalid
  | Incomplete : state -> status.

Definition eval_cstmap cs theta :=
  forall (id : Z) (c : cst),
    ZMaps.MapsTo id c cs -> eval_cst c theta.

Definition state_csts (s : state) :=
  match s with
  | (cs, clauses, hint) => cs
  end.

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

(*
Lemma check_inference_valid : forall (s : state) (cl : clause) (theta : asg),
  check_inference s cl = true -> eval_cstmap (state_csts s) theta -> eval_clause cl theta.
Proof.
  (* Add proof *)
Qed.
*)

Definition apply_inference (s : state) (id : Z) (cl : clause) := Invalid.
Definition apply_resolution (s : state) (id : Z) (cl : clause) (ants : list Z) := Invalid.

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
  
Definition apply_step (s : status) (d : step) :=
  match s with
  | Valid => Valid
  | Invalid => Invalid
  | Incomplete state =>
    match d with
    | Intro cid cl => apply_inference state cid cl
    | Hint cid => Incomplete (set_hint state cid)
    | Del cid => Incomplete (del_clause state cid)
    | Resolve cid cl ants => apply_resolution state cid cl ants
    end
  end.
    
