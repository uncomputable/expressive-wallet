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

Example next_coin_one :
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

Theorem expresses_leq :
forall w t,
expresses w t ->
S t <= sum w ->
expresses w (S t).
Proof.
unfold expresses. intros w t [F G] H. split.
- assumption.
- assumption.
Qed.

(* If a wallet expresses a target, *)
(* then the wallet plus the next coin can express the target plus one *)
(* In other words, adding the next coin makes progress. *)
Theorem expresses_next_coin :
forall l w t,
is_good l ->
expresses w t ->
expresses ((next_coin l (S t)) :: w) (S t).
Proof.
unfold expresses. intros l w t F [G H].
assert (E: 1 <= next_coin l (S t) <= S t).
{ split.
  - apply next_coin_ge_one. assumption.
  - apply next_coin_le. }
split.
- apply expressive_cons.
  + assumption.
  + lia.
- simpl. lia.
Qed.

(* Strategy to compute wallets that express a target *)
(* Start with the empty wallet *)
(* Keep the wallet from the previous step if it is large enough *)
(* Otherwise, add the next coin to the wallet *)
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

(* The strategy returns a wallet that expresses the target *)
Theorem strategy_correct :
forall l t,
is_good l ->
expresses (strategy l t) t.
Proof.
induction t; intros.
(* Target 0 *)
- apply expresses_zero. apply expressive_nil.
(* Target S t *)
- unfold strategy. fold (strategy l t).
  destruct (S t <=? sum (strategy l t)) eqn:G.
  (* Target is less equal sum of existing wallet *)
  (* Express target using existing wallet *)
  + apply leb_complete in G. apply expresses_leq.
    * apply IHt. assumption.
    * assumption.
  (* Target equals sum of existing wallet plus 1 *)
  (* Express target using wallet plus next coin *)
  + apply expresses_next_coin.
    * assumption.
    * apply IHt. assumption.
Qed.

(* Either *)
(* 1. The last coin was added because the wallet did not express the target, or *)
(* 2. The wallet was carried over from the previous step *)
Theorem strategy_monotonous :
forall l t x w,
strategy l (S t) = x :: w ->
~ expresses w (S t) \/ strategy l t = x :: w.
Proof.
induction t; intros.
(* Target S 0 *)
- unfold strategy in H. simpl in H. inversion H. left. intros Contra.
  unfold expresses in Contra. simpl in Contra. lia.
(* Target S (S t) *)
- unfold strategy in H. fold (strategy l (S t)) in H.
  destruct (S (S t) <=? sum (strategy l (S t))) eqn:G.
  (* Target is less equal sum from previous step *)
  + right. assumption.
  (* Target is greater than sum from previous step *)
  + left. apply leb_complete_conv in G. intros Contra.
    assert (F: strategy l (S t) = w).
    { injection H as _ H. subst. reflexivity. } subst.
    unfold expresses in Contra. destruct Contra as [_ Contra].
    lia.
Qed.

(* Discriminate tactic cannot handle this :/ *)
Theorem list_cons_neq :
forall (X: Type) (x: X) (l: list X),
x :: l <> l.
Proof.
induction l; intros H.
- inversion H.
- apply IHl. inversion H. repeat rewrite H2. reflexivity.
Qed.

(* The strategy returns a wallet *)
(* where the last coin cannot be removed relative to the previous step *)
(* In other words, the strategy adds coins only when necessary *)
(* TODO: What about removing coins from earlier steps? *)
Theorem strategy_minimal :
forall l t x w,
strategy l (S t) = x :: w ->
strategy l t = w ->
~ expresses w (S t).
Proof.
intros l t x w F G H. destruct t.
(* Target S 0 *)
- unfold strategy in G. subst.
  unfold expresses in H. destruct H as [_ H]. simpl in H. lia.
(* Target S (S t) *)
- apply strategy_monotonous in F. destruct F as [F|F].
  (* Previous wallet does not express target *)
  + apply F. assumption.
  (* Previous wallet equals current wallet *)
  + rewrite F in G. eapply list_cons_neq. apply G.
Qed.
