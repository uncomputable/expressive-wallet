Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lia.

(* A set of coin denominations is good *)
(* if it is sorted (in decreasing order) and *)
(* if the coin 1 is included. *)
(* In this case, our algorithms work and *)
(* all target amounts can be expressed. *)
Definition is_good (l : list nat) : Prop :=
StronglySorted ge l /\ exists l', l = l' ++ [1].

Example is_good1 :
~ is_good [].
Proof.
unfold is_good. intros [G [k H]]. destruct k; inversion H.
Qed.

Example is_good2 :
is_good [1].
Proof.
unfold is_good. split.
- repeat constructor.
- exists []. reflexivity.
Qed.

Example is_good3 :
~ is_good [2].
Proof.
unfold is_good. intros [G [k H]].
destruct k; inversion H. destruct k; inversion H2.
Qed.

Example is_good4 :
is_good [2;1].
Proof.
unfold is_good. split.
- repeat constructor.
- exists [2]. reflexivity.
Qed.

Example is_good5 :
~ is_good [1;2].
Proof.
unfold is_good. intros [G [k H]].
destruct k; inversion H. destruct k; inversion H2. destruct k; inversion H4.
Qed.

Theorem is_good_in_one :
forall l,
is_good l ->
In 1 l.
Proof.
unfold is_good. intros l [G [k H]]. rewrite H.
rewrite in_app_iff. right. simpl. left. reflexivity.
Qed.

Theorem is_good_le_one :
forall l,
is_good l ->
Forall (le 1) l.
Proof.
unfold is_good. induction l; intros; simpl.
- constructor.
- destruct H as [G [k H]]. constructor.
  + destruct a.
    * inversion G; subst. destruct k.
      -- inversion H.
      -- inversion H; subst. rewrite Forall_forall in H3. apply H3.
         rewrite in_app_iff. right. simpl. left. reflexivity.
    * lia.
  + destruct l.
    * constructor.
    * apply IHl. split.
      -- inversion G. assumption.
      -- destruct k.
        ++ inversion H.
        ++ exists k. inversion H. reflexivity.
Qed.

(* Return the largest coin that is less equal the target amount *)
Fixpoint next_coin (l: list nat) (t: nat) : nat :=
match l with
| [] => 0
| x :: ls => if x <=? t then x else next_coin ls t
end.

Compute (next_coin [5;2;1] 0).
Compute (next_coin [5;2;1] 1).
Compute (next_coin [5;2;1] 2).
Compute (next_coin [5;2;1] 3).
Compute (next_coin [5;2;1] 4).
Compute (next_coin [5;2;1] 5).

(* The next coin is less equal the target amount *)
Theorem next_coin_le :
forall l t,
next_coin l t <= t.
Proof.
induction l; intros; simpl.
- lia.
- destruct (a <=? t) eqn:H.
  + apply leb_complete. assumption.
  + apply IHl.
Qed.

(* The next coin is greater equal all coins below the target amount *)
(* In other words, the next coin is the target amount "rounded down" to the next denomination *)
Theorem next_coin_ge :
forall l x t,
is_good l ->
In x l ->
x <= t ->
x <= next_coin l t.
Proof.
induction l; intros; simpl.
- destruct H0.
- destruct H as [G [k H]]. destruct (a <=? t) eqn:F.
  + apply leb_complete in F. inversion H0; subst.
    * reflexivity.
    * inversion G; subst. rewrite Forall_forall in H6. apply H6 in H2. lia.
  + apply leb_complete_conv in F. inversion H0; try lia. apply IHl.
    * unfold is_good. split.
      -- inversion G. assumption.
      -- destruct k.
        ++ inversion H; subst. inversion H2.
        ++ exists k. inversion H. reflexivity.
    * assumption.
    * assumption.
Qed.


Lemma nil_eq_app :
forall (b: nat) k,
[] = k ++ [b] -> False.
Proof.
intros. destruct k.
- inversion H.
- inversion H.
Qed.

Lemma cons_eq_app :
forall (a b: nat) l k,
a :: l = k ++ [b] ->
(l = [] /\ k = [] /\ a = b) \/ exists l', l = l' ++ [b].
Proof.
intros a b l k. revert l a b. induction k; intros; simpl.
- left. simpl in H. destruct l.
  + inversion H; subst. repeat (split; try reflexivity).
  + inversion H.
- right. destruct l.
  + inversion H; subst. destruct k.
    * inversion H2.
    * inversion H2.
  + rewrite <- app_comm_cons in H. inversion H; subst.
    apply IHk in H2. destruct H2 as [[A[B C]]|_].
    * subst. exists []. reflexivity.
    * inversion H; subst. exists k. assumption.
Qed.

Theorem next_coin_ge_one :
forall l t,
is_good l ->
1 <= next_coin l (S t).
Proof.
intros. apply next_coin_ge.
- assumption.
- apply is_good_in_one. assumption.
- lia.
Qed.

Theorem next_coin_one :
forall l,
is_good l ->
next_coin l 1 = 1.
Proof.
intros.
assert (Lt: next_coin l 1 <= 1).
{ apply next_coin_le. }
assert (Gt: 1 <= next_coin l 1).
{ apply next_coin_ge.
  - assumption.
  - apply is_good_in_one. assumption.
  - lia. }
lia.
Qed.

Example next_coin_zero_false :
forall l,
is_good l ->
~ next_coin l 0 = 1.
Proof.
intros. assert (G: next_coin l 0 <= 0). { apply next_coin_le. }
lia.
Qed.

Theorem leq_eq :
forall x y,
x <= y ->
x + (y - x) = y.
Proof.
intros. symmetry. apply Arith_prebase.le_plus_minus_stt. assumption.
Qed.

Theorem leq_eq_ex :
forall x y,
x <= y -> exists z,
z <= y /\ x + z = y.
Proof.
intros. exists (y - x). split.
- apply Nat.le_sub_l.
- apply leq_eq. assumption.
Qed.

Theorem next_coin_gap :
forall l t,
is_good l -> exists x,
x <= t /\ next_coin l (S t) + x = (S t).
Proof.
intros. exists (S t - next_coin l (S t)). split.
- apply next_coin_ge_one with (t := t) in H. destruct (next_coin l (S t)).
  + lia.
  + lia.
- apply leq_eq. apply next_coin_le.
Qed.

(* Set `l` is a subset of set `k` if all elements from `l` are in `k` *)
Definition subset (l k: list nat) : Prop :=
forall x,
In x l -> In x k.

Theorem subset_nil :
forall l,
subset [] l.
Proof.
unfold subset. intros. inversion H.
Qed.

Theorem subset_cons :
forall l k x,
subset l k ->
subset l (x :: k).
Proof.
unfold subset. intros. apply H in H0. eapply in_cons in H0. apply H0.
Qed.

Theorem subset_eq :
forall l k x,
subset l k ->
subset (x :: l) (x :: k).
Proof.
unfold subset. destruct l; intros; simpl.
- inversion H0; subst.
  + left. reflexivity.
  + right. inversion H1.
- inversion H0; subst.
  + left. reflexivity.
  + apply H in H1. right. assumption.
Qed.

(* We sum a list via left folding *)
Definition sum (l: list nat) : nat :=
fold_left Nat.add l 0.

(* Wallet `w` expresses target amount `t` if *)
(* for each amount 0 <= x <= t there is a subset w' of w that sums to x *)
Definition can_express (w: list nat) (t: nat) : Prop :=
forall x,
0 <= x <= t -> exists w',
subset w' w /\ sum w' = t.

Theorem next_coin_express :
forall t w l,
is_good l ->
can_express w t ->
can_express ((next_coin l (S t)) :: w) (S t).
Proof.
unfold is_good. unfold can_express. induction t; intros; simpl.
- exists [1]. split.
  + unfold subset. intros y G. rewrite next_coin_one.
    * inversion G; subst.
      -- simpl. left. reflexivity.
      -- inversion H2.
    * assumption.
  + reflexivity.
- admit.
Admitted.

Fixpoint strategy (l: list nat) (t: nat) : list nat :=
match t with
| 0 => []
| S t' => let wallet := strategy l t' in
          if t <=? sum wallet then wallet else (next_coin l t) :: wallet
end.

Compute (strategy [5;2;1] 0).
Compute (strategy [5;2;1] 1).
Compute (strategy [5;2;1] 2).
Compute (strategy [5;2;1] 3).
Compute (strategy [5;2;1] 4).
Compute (strategy [5;2;1] 5).

Theorem strategy_express :
forall l t,
can_express (strategy l t) t.
Admitted.
