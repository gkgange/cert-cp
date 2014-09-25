Require Import ZArith.
Require Import Bool.
Require Import bounds.
Require Import prim.

(* Really should add some stuff regarding
 * non-negative variables. *)
Record task : Type := mkTask {
  duration : Z ;
  resource : Z ;
  svar : ivar 
}.

Record vartask : Type := mkVarTask {
  vt_dur: ivar ;
  vt_res : ivar ;
  vt_svar : ivar
}.

Record cumul : Type := mkCumul {
  tasks : list task ;
  limit : Z
}.

Fixpoint eval_usage (ts : list task) (time : Z) (theta : asg) :=
  match ts with
  | nil => 0%Z
  | cons t ts' =>
      let tstart := eval_ivar t.(svar) theta in
      let curr :=
        if Z_leb tstart time && Z_ltb time (tstart + t.(duration)) then
          t.(resource)
        else 0 in
      curr + eval_usage ts' time theta
  end.

Definition eval_cumul (c : cumul) (theta : asg) :=
  forall (time : Z), eval_usage c.(tasks) time theta <= c.(limit).

(* Check whether the ~cl -> [| s[t] >= lb |] /\ [| s[t]+d[t] < ub |]. *)


Fixpoint span_area (ts : list task) (cl : clause) (lb ub : Z) :=
  match ts with
  | nil => 0%Z
  | cons t ts' =>
     if containedb t cl lb ub = true then 
       t.(resource)*t.(duration) + (span_area ts' cl lb ub)
     else
       span_area ts' cl lb ub.

Definition check_cumul (c : cumul) (cl : clause) : bool := false.

Theorem check_cumul_valid : forall (c : cumul) (cl : clause),
  check_cumul c cl = true -> implies (eval_cumul c) (eval_clause cl).
Proof.
  unfold check_cumul. intros. discriminate.
Qed.

Definition CumulConstraint (C : Constraint) : Constraint :=
  mkConstraint (cumul) (eval_cumul) (check_cumul) (check_cumul_valid).
