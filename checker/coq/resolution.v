(* Resolution of clauses. *)
Require Import prim.
Require Lists.List.
Require Import domset.

(* Actually, we can get away with doing deduplication in a preprocess;
 * soundness doesn't rely on preserving the proof semantics, just the
 * _existence_ of a correct proof. *)
Fixpoint dedup (cl : clause) := 
  match cl with
  | nil => nil
  | cons l cl' =>
      if List.existsb (lit_eqb l) cl'
      then
        (dedup cl')
      else
        cons l (dedup cl')
  end.

(* FIXME: Implement prop_clause. *)
Definition prop_clause (ds : domset) (cl : clause) := ds.
(*
  match cl with
  | nil => ds (* FIXME - should be empty domain. *)
  | cons l cl' =>
    if lit_unsat ds l then
      prop_clause ds cl'
    else
      if clause_unsat ds cl' then
        
      else
        ds
  end.
*)

Lemma prop_clause_valid : forall (ds : domset) (cl : clause) (theta : asg),
    eval_domset ds theta -> eval_domset (prop_clause ds cl) theta.
Proof.
  intros; unfold prop_clause; assumption.
Qed.

Fixpoint unit_prop (ds : domset) (cs : list clause) :=
  match cs with
  | nil => ds
  | cons cl cs' =>
      prop_clause (unit_prop (prop_clause ds cl) cs') cl
  end.
Lemma unit_prop_valid : forall (ds : domset) (cs : list clause) (theta : asg),
  eval_domset ds theta -> eval_domset (unit_prop ds cs) theta.
Proof.
  unfold unit_prop; intros; induction cs.
    assumption.
    fold unit_prop in *.
    apply prop_clause_valid; apply IHcs; now apply prop_clause_valid.
Qed.
  

(* FIXME: Implement resolvable. *)
Definition resolvable (cl : clause) (ants : list clause) :=
  false.

Theorem resolvable_valid : forall cl ants,
  resolvable cl ants = true -> forall theta, eval_clauses ants theta -> eval_clause cl theta.
Proof.
  intros cl ants; unfold resolvable; discriminate.
Qed.
