Inductive binary_tree : Type :=
  Leaf : nat -> binary_tree
| Node : binary_tree -> binary_tree -> binary_tree.

Check binary_tree_ind.

(*
binary_tree_ind
     : forall P : binary_tree -> Prop,
       (forall n : nat, P (Leaf n)) ->
       (forall b : binary_tree,
        P b -> forall b0 : binary_tree, P b0 -> P (Node b b0)) ->
       forall b : binary_tree, P bC
 *)

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall i : nat,
        P i -> P (S i) -> P (S (S i)))
    -> forall n : nat,
        P n. 
Proof.
  intros P H_bc0 H_bc1 H_is n.
  assert (both : P n /\ P (S n)).
  induction n as [ | n' [IH_n' IH_Sn']].
  split.
  exact H_bc0.
  exact H_bc1.

  split.
  exact IH_Sn'.
  Check (H_is n' IH_n' IH_Sn').
  exact (H_is n' IH_n' IH_Sn').

  destruct both as [ly _].
  exact ly.
Qed.

Lemma nat_ind1 :
  forall P : nat -> Prop,
    P 0 ->
    (forall i : nat,
        P i -> P (S i))
    -> forall n : nat,
        P n. 
Proof.
  intros P H_bc H_is n.
  induction n as [ | | n'' IH_n'' IH_Sn''] using nat_ind2.
  exact H_bc.

  Check (H_is 0 H_bc).
  exact (H_is 0 H_bc).

  Check (H_is (S n'') IH_Sn'').
  exact (H_is (S n'') IH_Sn'').
Qed.

Lemma nat_ind1' :
  forall P : nat -> Prop,
    P 0 ->
    (forall i : nat,
        P i -> P (S i))
    -> forall n : nat,
        P n. 
Proof.
   intros P H_bc H_is n.
   induction n as [ | n' IH_n'] using nat_ind1.

   exact H_bc.
   exact (H_is n' IH_n').
Qed.


Lemma nat_ind3 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 -> 
    (forall i : nat,
        P i ->
        P (S i) ->
        P (S (S i)) ->
        P (S (S (S i))))
    -> forall n : nat,
        P n. 
Proof.
  intros P H_bc0 H_bc1 H_bc2 H_is n.
  assert (all_three : P n /\ P (S n) /\ P (S (S n))).
  induction n as [ | n'' [IH_n'' [IH_Sn'' IH_SSn'']]].
  split.
  exact H_bc0.
  split.
  exact H_bc1.
  exact H_bc2.
  split.
  exact IH_Sn''.
  split.
  exact IH_SSn''.
  Check (H_is n'' IH_n'' IH_Sn'' IH_SSn'').
  exact (H_is n'' IH_n'' IH_Sn'' IH_SSn'').

  destruct all_three as [ly [_ _]].
  exact ly.
  Restart.

  intros P H_bc0 H_bc1 H_bc2 H_is n.
  assert (both : P n /\ P (S n)).
  induction n as [ | | n''[IH_n'' IH_Sn''][_ IH_SSn'']] using nat_ind2.
  split.
  exact H_bc0.
  exact H_bc1.

  split.
  exact H_bc1.
  exact H_bc2.

  split.
  exact IH_SSn''.
  Check (H_is n'' IH_n'' IH_Sn'' IH_SSn'').
  exact (H_is n'' IH_n'' IH_Sn'' IH_SSn'').
  
  destruct both as [ly _].
  exact ly.
Qed.

Require Import Arith.


Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Fixpoint and_until (P : nat -> Prop) (n : nat) : Prop :=
  match n with
  | 0 =>
    P 0
  | S n' =>
    P n /\ and_until P n'
  end.

Lemma unfold_and_until_0:
  forall (P : nat -> Prop),
    and_until P 0 = P 0.
Proof.
  unfold_tactic and_until.
Qed.
  
Lemma unfold_and_until_S:
  forall (P : nat -> Prop) (n' : nat),
    and_until P (S n') =
    (P (S n') /\ and_until P n').
Proof.
  unfold_tactic and_until.
Qed.


Lemma about_and_until :
  forall (P : nat -> Prop)
         (x : nat),
    and_until P x -> P x.
Proof.
  intros P [ | x'].

  rewrite -> unfold_and_until_0.
  intro H_P0.
  exact H_P0.

  rewrite -> unfold_and_until_S.
  intros [H_PS _].
  exact H_PS.
Qed.

Lemma nat_ind_cov :
  forall P : nat -> Prop,
    P 0 ->
    (forall i : nat,
        and_until P i -> P (S i)) ->
    forall n : nat,
      P n.
Proof.
  intros P H_bc H_is.
  assert (P' : forall m : nat, and_until P m).
    intro m.
    induction m as [ | m' IHm'].
    rewrite -> unfold_and_until_0.
    exact H_bc.

    rewrite -> unfold_and_until_S.
    split.
      Check (H_is m' IHm').
      exact (H_is m' IHm').
      exact IHm'.

  intros [ | n'].
  exact H_bc.

  Check (H_is n' (P' n')).
  exact (H_is n' (P' n')).
Qed.

Lemma strong_induction:
  forall P : nat -> Prop,
    P 0 ->
    (forall m : nat,
        (forall k, (k <= m -> P k))
        -> P (S m)) ->
    forall n : nat,
      P n.
Proof.
  Admitted.
  