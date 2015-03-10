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

Record SolCheck (C : Constraint) := mkSolCheck
  {
    sol_check : C.(T) -> zsol -> bool ;
    sol_check_valid : forall (x : C.(T) ) (zs : zsol),
      (sol_check x zs = true) ->
        implies (eval_zsol zs) (C.(eval) x)
  }.