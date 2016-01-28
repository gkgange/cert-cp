(* Stuff for dealing with solutions. *)(* Computing domains/bounds from the complement of a clause. *)
Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import FSets.FMapFacts.
Require Import zset.
Require Import map.
Require Import prim.
Require Import bounds.
Require Import domain.

(* Partial solution - mapping of variables to integers. *)
Definition partial_zsol : Type := zmap Z.
Definition partial_bsol : Type := zmap bool.

Definition eval_partial_zsol zs x :=
  match ZMaps.find zs x with
  | Some k => k
  | None => 0%Z
  end.
Definition eval_partial_bsol bs x :=
  match ZMaps.find bs x with
  | Some b => b
  | None => false
  end.

Definition asg_of_partial_sol zs bs :=
  ((eval_partial_zsol zs), (eval_partial_bsol bs)).

Fixpoint eval_alist_zsol zs x :=
  match zs with
  | nil => 0%Z
  | cons (x', k) zs' =>
      if Z_eqb x x' then
        k
      else
        eval_alist_zsol zs' x
  end.

Definition asg_of_alist zs :=
  ((eval_alist_zsol zs), (fun (bv : bvar) => false)).

(*
Fixpoint zasg_of_list zl :=
  match zl with
  | [] => ZMaps.empty
  | cons (x, k) :: zl' =>
      match ZMaps.find zl x with
      | Some b => 
          *)

(* Definition asg_of_list (zl, bl) := (zasg_of_list zl, basg_of_list bl) *)
(*
Definition zsol : Type := zmap Z.

Definition eval_zsol zs theta :=
  forall (x : ivar) (v : Z),
    ZMaps.MapsTo x v zs -> eval_ivar x theta = v.

Definition zsol_val (zs : zsol) (x : ivar) :=
  ZMaps.find x zs.

Lemma zsol_val_valid : forall (zs : zsol) (x : ivar) (v : Z),
  zsol_val zs x = Some v ->
    forall theta, eval_zsol zs theta -> eval_ivar x theta = v.
Proof.
  intros zs x v; unfold zsol_val; intros.
  unfold eval_zsol in H0.
  now apply ZMaps.find_2, H0 in H.
Qed.
*)

Record SolCheck (C : Constraint) := mkSolCheck
  {
    sol_check : C.(T) -> asg -> bool ;
    sol_check_valid : forall (x : C.(T) ) (sol : asg),
      (sol_check x sol = true) -> C.(eval) x sol
  }.

Theorem evalb_clause_valid : forall (cl : clause) (sol : asg), evalb_clause cl sol = true -> eval ClauseCon cl sol.
Proof.
  intros; now rewrite <- evalb_clause_iff.
Qed.
Definition CheckClauseSol := mkSolCheck ClauseCon evalb_clause evalb_clause_valid.