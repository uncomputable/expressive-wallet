Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lia.

(* A set of coin denominations is good *)
(* if it is sorted (in decreasing order) and *)
(* if the coin 1 is included. *)
(* In this case, our algorithms work and *)
(* all targets can be expressed. *)
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

(* Return the largest coin that is less equal the target *)
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

(* The next coin is less equal the target *)
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

(* The next coin is greater equal all coins below the target *)
(* In other words, the next coin is the target "rounded down" *)
(* to the next denomination *)
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

(* Every element in the subset is also in the superset *)
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

(* Sum a list via folding *)
Definition sum (l: list nat) : nat :=
fold_right Nat.add 0 l.

Compute (sum [1;2;3]).

Theorem sum_cons :
forall (x: nat) l,
sum (x :: l) = sum l + x.
Proof.
intros. unfold sum. simpl. lia.
Qed.

(* A wallet is expressive *)
(* if each amount below the maximum is equal to the sum of a subset of the wallet *)
(* The maximum is the sum of all coins *)
Definition expressive (w: list nat) : Prop :=
forall x,
x <= sum w -> exists w',
subset w' w /\ sum w' = x.

(* The empty wallet is expressive *)
Theorem expressive_nil :
expressive [].
Proof.
unfold expressive. intros. assert (G: x = 0). { simpl in H. lia. } subst.
exists []. split.
- apply subset_nil.
- reflexivity.
Qed.

Example expressive1 :
expressive [].
Proof.
apply expressive_nil.
Qed.

Example expressive2 :
expressive [1].
Proof.
unfold expressive. intros. destruct x.
(* Express 0 *)
- exists []. split; try reflexivity. apply subset_nil.
(* Express 1 *)
- assert (G: x = 0). { simpl in H. lia. } subst.
  exists [1]. split; try reflexivity. apply subset_eq. apply subset_nil.
Qed.

Example expressive3 :
~ expressive [2].
Proof.
unfold expressive. intros H. specialize (H 1).
assert (G: 1 <= sum [2]). { simpl. lia. }
apply H in G. destruct G as [w' [F G]].
(* Fail to derive contradiction from *)
(* subset w' [2] (meaning that w' = [] or w' = [2]) and *)
(* sum w' = 1 (meaing that w' = [1]) *)
Admitted.

Example expressive4 :
expressive [1;2].
Proof.
unfold expressive. intros. destruct x.
(* Express 0 *)
- exists []. split; try reflexivity. apply subset_nil.
- destruct x.
  (* Express 1 *)
  + exists [1]. split; try reflexivity. apply subset_eq. apply subset_nil.
  + destruct x.
    (* Express 2 *)
    * exists [2]. split; try reflexivity. apply subset_cons. apply subset_eq. apply subset_nil.
    (* Express 3 *)
    * assert (G: x = 0). { simpl in H. lia. } subst.
      exists [1;2]. split; try reflexivity. repeat apply subset_eq. apply subset_nil.
Qed.

Example expressive5 :
expressive [2;1].
Proof.
unfold expressive. intros. destruct x.
(* Express 0 *)
- exists []. split; try reflexivity. apply subset_nil.
- destruct x.
  (* Express 1 *)
  + exists [1]. split; try reflexivity. apply subset_cons. apply subset_eq. apply subset_nil.
  + destruct x.
    (* Express 2 *)
    * exists [2]. split; try reflexivity. apply subset_eq. apply subset_nil.
    (* Express 3 *)
    * assert (G: x = 0). { simpl in H. lia. } subst.
      exists [2;1]. split; try reflexivity. repeat apply subset_eq. apply subset_nil.
Qed.

(* If a wallet is expressive, *)
(* then we can add a coin between 0 and the wallet sum + 1 *)
(* to obtain another expressive wallet *)
Theorem expressive_cons :
forall w y,
expressive w ->
y <= S (sum w) ->
expressive (y :: w).
Proof.
unfold expressive. induction w; intros; simpl.
(* Wallet [] *)
- simpl in H0. inversion H0; subst.
  (* New wallet 1 :: [] *)
  + inversion H1; subst.
    (* Express 1 *)
    * exists [1]. split; try reflexivity. apply subset_eq. apply subset_nil.
    (* Express 0 *)
    * inversion H3; subst. exists []. split; try reflexivity. apply subset_nil.
  (* New wallet 0 :: [] *)
  (* Express 0 *)
  + inversion H3; subst. inversion H1. exists []. split; try reflexivity. apply subset_nil.
(* Wallet (a :: w) *)
- destruct (x <=? sum (a :: w)) eqn:G.
  (* Express x where x <= sum (a :: w) *)
  (* Use existing subset of wallet (a :: w) *)
  + apply leb_complete in G. apply H in G. destruct G as [w' [F G]].
    exists w'. split; try assumption. apply subset_cons. assumption.
  (* Express x where sum (a :: w) < x <= sum (a :: w) + y *)
  (* The difference z between x and y is small *)
  (* x = y + z for some 1 <= z <= sum (a :: w) *)
  (* Take [y] and add the subset for z from wallet (a :: w) *)
  + apply leb_complete_conv in G.
    assert (F: exists z, z <= sum (a :: w) /\ x = y + z).
    { simpl in H1. apply leq_eq_ex in H1. destruct H1 as [z' [E F]].
      (* Truncated subtraction requires extra hypotheses *)
      assert (D: x = y + sum (a :: w) - z'). { simpl. lia. }
      assert (C: z' <= y). { lia. }
      exists (sum (a :: w) - z'). lia. }
    destruct F as [z [E F]]. assert (E': z <= sum (a :: w)). { lia. }
    apply H in E'. destruct E' as [w' [C D]].
    exists (y :: w'). split.
    * apply subset_eq. assumption.
    * rewrite F. simpl. lia.
Qed.

(* A wallet expresses a target *)
(* if the wallet is expressive and *)
(* if the wallet is large enough to sum to the target *)
Definition expresses (w: list nat) (t: nat) : Prop :=
expressive w /\ t <= sum w.

Theorem expresses_zero :
forall w,
expressive w ->
expresses w 0.
Proof.
unfold expresses. intros. split.
- assumption.
- lia.
Qed.

(* If a wallet expresses a target, *)
(* then the wallet plus the next coin can express the target plus one *)
(* In other words, adding the next coin makes progress. *)
Theorem expresses_next_coin :
forall t w l,
is_good l ->
expresses w t ->
expresses ((next_coin l (S t)) :: w) (S t).
Proof.
Admitted.
(* TODO: Prove next_coin l (S t) <= S (sum w) *)
(* Then use expressive_cons *)
(*
unfold expresses. destruct t; intros; simpl.
- destruct x.
  (* Amount x = 0 *)
  + exists []. split.
    * apply subset_nil.
    * reflexivity.
  (* Amount x = 1 *)
  + exists [1]. assert (G: x = 0). { lia. } subst. split.
    * rewrite next_coin_one.
      -- apply subset_eq. apply subset_nil.
      -- assumption.
    * reflexivity.
- destruct (x =? S (S t)) eqn:G.
  (* Amount x = S (S t)) *)
  (* Construct subset from next_coin l (S (S t)) and existing subsets of wallet w *)
  + rewrite Nat.eqb_eq in G; subst.
    assert (G: exists x, x <= S t /\ next_coin l (S (S t)) + x = S (S t)).
    { apply next_coin_gap. assumption. } destruct G as [x [F G]].
    apply (H0 x) in F. destruct F as [w' [E F]].
    exists (next_coin l (S (S t)) :: w'). split.
    * apply subset_eq. assumption.
    * rewrite sum_cons. lia.
  (* Amount x <= S t *)
  (* Take existing subset of wallet w *)
  + rewrite Nat.eqb_neq in G. assert (F: x <= S t). { lia. }
    apply H0 in F. destruct F as [w' [E F]].
    exists w'. split.
    * apply subset_cons. assumption.
    * assumption.
Qed.
*)

Fixpoint strategy (l: list nat) (t: nat) : list nat :=
match t with
| 0 => []
| S t' => let w := strategy l t' in
          if t <=? sum w then w else (next_coin l t) :: w
end.

Compute (strategy [5;2;1] 0).
Compute (strategy [5;2;1] 1).
Compute (strategy [5;2;1] 2).
Compute (strategy [5;2;1] 3).
Compute (strategy [5;2;1] 4).
Compute (strategy [5;2;1] 5).

Theorem expresses_strategy :
forall l t,
expresses (strategy l t) t.
Admitted.
