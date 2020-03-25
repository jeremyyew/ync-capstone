(* FPP_8b_annotated.v *)
(* was: *)
(* FPP_8b.v *)
(* YSC3236 2018-2019, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 11 October 2018 *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

Definition test_even (candidate: nat -> bool) : bool :=
  (candidate 0 =b= true)
    &&
    (candidate 1 =b= false)
    &&
    (candidate 2 =b= true)
    &&
    (candidate 3 =b= false)
    (* etc. *)
.


Definition test_odd (candidate: nat -> bool) : bool :=
  (candidate 0 =b= false)
    &&
    (candidate 1 =b= true)
    &&
    (candidate 2 =b= false)
    &&
    (candidate 3 =b= true)
    (* etc. *)
.

Fixpoint is_odd (n : nat) : bool :=
  match n with
  | 0 => false
  | S n' => is_even n'
  end
with is_even (n : nat) : bool :=
  match n with
  | 0 => true
  | S n' => is_odd n'
  end.

Compute test_odd is_odd.
Compute test_even is_even.

Lemma fold_unfold_is_even_O :
  is_even 0 = true.
Proof.
  fold_unfold_tactic is_even.
Qed.

Lemma fold_unfold_is_even_S :
  forall (n : nat),
    is_even (S n) = is_odd n.
Proof.
  fold_unfold_tactic is_even
  .
Qed.

Lemma fold_unfold_is_odd_O :
  is_odd 0 = false.
Proof.
  fold_unfold_tactic is_odd.
Qed.

Lemma fold_unfold_is_odd_S :
  forall (n : nat),
    is_odd (S n) = is_even n.
Proof.
  fold_unfold_tactic is_odd.
Qed.

Proposition disjunction_is_commutative :
  forall P Q : Prop,
    P \/ Q <-> Q \/ P.
(* O: is the bi-implication really necessary? *)
Proof.
  intros P Q.
  split.
  
  - intro H_P_or_Q.
    destruct H_P_or_Q as [H_P | H_Q].
    
    right.
    exact H_P.
    left.
    exact H_Q.
    
  - intro H_Q_or_P.
    destruct H_Q_or_P as [H_Q | H_P].
    
    right.
    exact H_Q.
    left.
    exact H_P.
    Show Proof.
Qed.


Lemma n_is_either_even_or_odd :
  forall (n : nat),
    is_even n = true \/ is_odd n = true.
Proof.
  intro n.
  induction n as [ | n' IHn'].

  - rewrite -> fold_unfold_is_even_O.
    left.
    reflexivity.

  - rewrite -> (fold_unfold_is_even_S (n')).
    rewrite -> (fold_unfold_is_odd_S (n')).
    Check disjunction_is_commutative.
(* O: You are abusing Coq here: apply works for an implication, not a bi-implication.  Mindfully use destruct first. *)
    apply (disjunction_is_commutative (is_odd n' = true) (is_even n' = true)).
    exact IHn'.
Qed.

Lemma n_is_even_implies_successor_of_n_is_odd :
  forall (n : nat),
    is_even n = true ->
    is_odd (S n) = true.
Proof.
  intro n.
  intro H_is_even.
  rewrite -> (fold_unfold_is_odd_S n).
  apply H_is_even.
(* O: You might as well use exact here. *)
Qed.

Lemma n_is_odd_implies_successor_of_n_is_even :
  forall (n : nat),
    is_odd n = true ->
    is_even (S n) = true.
Proof.
  intro n.
  intro H_is_odd.
  rewrite -> (fold_unfold_is_even_S n).
  apply H_is_odd.
Qed.

Lemma evenness_of_additions :
  forall (n m : nat),
    (is_odd n = true ->
     is_odd m = true ->
     is_even (n + m) = true)
    /\
    (is_odd n = true ->
     is_even m = true ->
     is_odd (n + m) = true)
    /\
    (is_even n  = true ->
     is_odd m = true ->
     is_odd (n + m) = true)
    /\
    (is_even n = true ->
     is_even m = true ->
     is_even (n + m) = true).
Proof.
  intro n.
  induction n as [ | n' IHn'].

  - intro m.
    rewrite -> (fold_unfold_is_odd_O).
    rewrite -> (fold_unfold_is_even_O).
    rewrite -> (plus_O_n).
    split.

    * intro H_absurd.
      discriminate H_absurd.

    * split.

    + intro H_absurd.
      discriminate H_absurd.

    + split.

      ** intros H_1 H_2.
         exact H_2.

      ** intros H_1 H_2.
         exact H_2.

  - intro m.
    rewrite -> (fold_unfold_is_even_S).
    rewrite -> (fold_unfold_is_odd_S).
    Search (S _ + _ = _).
    rewrite -> plus_Sn_m.
    rewrite -> (fold_unfold_is_odd_S).
    rewrite -> (fold_unfold_is_even_S).
    split.

    * apply (IHn' m).

    * split.

      ** apply (IHn' m).

      ** split.

      ++ apply (IHn' m).

      ++ apply IHn'.
Qed.

(* O: Wouldn't be more natural to state:
  forall n : nat,
    is_even n = true ->
    forall m : nat,
      is_even (n * m) = true.
   ?
*)

Proposition product_of_even_and_any_number_is_even :
  forall (n m : nat),
    is_even n = true ->
    is_even (n * m) = true.
Proof.
  intro n.
  induction m as [ | m' IHm'].

  - intro H_is_even.
    Search (_ * 0 = 0).
    rewrite -> (Nat.mul_0_r).
    rewrite -> (fold_unfold_is_even_O).
    reflexivity.

  - intro H_is_even.
    Search (_ * S _ = _).
    rewrite -> Nat.mul_succ_r.
    rewrite -> Nat.add_comm.
    Check evenness_of_additions.
    apply (evenness_of_additions n (n * m')).
(* O: Again, you are abusing Coq here.  Mindfully use destruct first. *)
    apply H_is_even.
(* O: How about:
    Check (IHm' H_is_even).
   ?
*)
    apply IHm'. (*Which tells us that if n is even, then n * m' is even. So we need the fact that n is even. *)
    apply H_is_even.
Qed.

Corollary product_of_any_number_and_even_is_even :
  forall (n m : nat),
    is_even m = true ->
    is_even (n * m) = true.
Proof.
  intros n m.
  revert m. (* Will not fall for this again. *)
  induction n as [ | n' IHn'].

  - intro m.
    intro H_is_even.
    rewrite -> (Nat.mul_0_l).
    rewrite -> (fold_unfold_is_even_O).
    reflexivity.

  - intro m.
    intro H_is_even.
    rewrite -> Nat.mul_succ_l.
    rewrite -> Nat.add_comm.
    Check evenness_of_additions.
    apply (evenness_of_additions m (n' * m)).
    apply H_is_even.
    apply IHn'.
    apply H_is_even.
Qed.
(* O: Why is this a corollary?  You have a full-fledged proof.
      A corollary would be to use Nat.nat_comm and then product_of_even_and_any_number_is_even.
*)

Theorem the_product_of_two_consecutive_nat_numbers_is_even :
  forall (n : nat), is_even (mult n (S n)) = true.
Proof.
  intro n.
(* O: How about using n_is_either_even_or_odd here?
  destruct (n_is_either_even_or_odd n) as [H_n | H_n].
*)

  case n as [ | n' IHn'].

  - Search (0 * _ = 0).
    rewrite -> (Nat.mul_0_l 1).
    rewrite -> (fold_unfold_is_even_O).
    reflexivity.

  - Check Nat.mul_succ_l.
    rewrite -> Nat.mul_succ_l.
    rewrite -> Nat.add_succ_r.
    rewrite -> Nat.add_succ_r.
    rewrite -> fold_unfold_is_even_S.
    rewrite -> fold_unfold_is_odd_S.
    rewrite -> Nat.mul_comm.
    Search (S _ * _ = _).
    rewrite -> (Nat.mul_succ_l).
    rewrite -> (Nat.mul_succ_l).
    Abort.
