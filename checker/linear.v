Require Import ZArith.
Require Import prim.
Require Import bounds.

Definition linterm : Type := (Z * ivar)%type.

(* c_1 x_1 + ... + c_n x_n <= k *)
Definition lin_leq : Type := ((list linterm) * Z)%type.

Definition eval_linterm term theta := (fst term)*(eval_ivar (snd term) theta).

Fixpoint eval_linsum ts theta :=
  match ts with
  | nil => 0%Z
  | cons t ts' => (eval_linterm t theta) + (eval_linsum ts' theta)
  end.

(* FIXME: Doesn't handle negative coefficients. *)
Definition linterm_lb_from_negclause (t : linterm) (cl : clause) :=
  if Z_lt_dec (fst t) 0 then
    Unbounded
  else
    match lb_from_negclause (snd t) cl with
    | Unbounded => Unbounded
    | Bounded l => Bounded ((fst t)*l)
    end.

Theorem linterm_lb_from_negclause_valid :
  forall (t : linterm) (cl : clause) (theta : asg),
    ~eval_clause cl theta ->
      sat_lb (linterm_lb_from_negclause t cl) (eval_linterm t theta).
Proof.
  intros. destruct t. unfold linterm_lb_from_negclause.
  unfold eval_linterm.
  assert (eval_lb i (lb_from_negclause i cl) theta) as Hsatlb.
  apply lb_from_negclause_valid; exact H.
  unfold eval_lb in Hsatlb.


(* Compute the lb of a linear sum implied by ~cl. *)
Fixpoint linsum_lb_from_negclause (ts : list linterm) (cl : clause) :=
  match ts with
  | nil => Bounded 0%Z
  | cons t ts' =>
      bound_add (linterm_lb_from_negclause t cl)
                (linsum_lb_from_negclause ts' cl)
  end.

Theorem linsum_lb_valid : forall (ts : list linterm) (cl : clause) (theta : asg),
  ~ eval_clause cl theta ->
      sat_lb (linsum_lb_from_negclause ts cl) (eval_linsum ts theta).
Proof.
  intros. unfold sat_lb. induction ts.
  unfold linsum_lb_from_negclause; unfold eval_linsum. apply Zle_refl.
  unfold linsum_lb_from_negclause ; fold linsum_lb_from_negclause.
  unfold eval_linsum; fold eval_linsum.
  unfold eval_linterm.
  assert (eval_lb (snd a) (lb_from_negclause (snd a) cl) theta).
  apply lb_from_negclause_valid; exact H.
(*
Theorem linterm_lb_valid : forall (t : linterm) (cl : clause) (theta : asg),
  ~ eval_clause cl theta -> 
*)

Definition eval_lincon lincon (theta : asg) :=
  (eval_linsum (fst lincon) theta) <= (snd lincon).

Fixpoint lincon_implies_rec (ts : list linterm) (k : Z) (cl : clause) :=
  match ts with
  | nil => Z_ltb k 0%Z
  | cons t ts' =>
    match linterm_lb_from_negclause t cl with
    | Unbounded => false
    | Bounded k' =>
      lincon_implies_rec ts' (k - k') cl
    end
  end.
  
Fixpoint lincon_implies (lincon : lin_leq) (cl : clause) : bool :=
  lincon_implies_rec (fst lincon) (snd lincon) cl.

Theorem lincon_implies_valid : forall (lincon : lin_leq) (cl : clause),
  lincon_implies lincon cl = true ->
    implies (eval_lincon lincon) (eval_clause cl).
Proof.
  intros. unfold implies. intros.
  induction cl.
  assert eval_lincon 
  unfold lincon_implies. unfold lincon_implies_rec. destruct nil.
