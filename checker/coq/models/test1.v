(* Infrastructure test for checking. *)
Require bounds.
Require model.
Require log.
Require map.
Require Import List.
Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.

(* x0 + x1 <= 5 *)
Definition m_cstrs : model.csts := [ (0, model.Lin ([(1, 0); (1, 1)], 5)) ].
(* x0 in [3, 10], x1 in [3, 10] *)
Definition m_bounds : list bounds.model_bound := [ (0, 3, 10) ; (1, 3, 10) ].
Definition m : model.model := (m_bounds, m_cstrs).

Definition m_proof := [ log.Hint 0 ; log.Intro 0 [] ].

Theorem m_is_unsat : model.model_unsat m.
Proof.
  apply log.certify_unsat_list_valid with (ss := m_proof).
  now vm_compute.
Qed.