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


(* FIXME: Implement resolvable. *)
Definition resolvable (cl : clause) (ants : list clause) :=
  false.

Theorem resolvable_valid : forall cl ants,
  resolvable cl ants = true -> forall theta, eval_clauses ants theta -> eval_clause cl theta.
Proof.
  intros cl ants; unfold resolvable; discriminate.
Qed.
