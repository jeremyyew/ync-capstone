(* week-14_streams.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Fri 17 Nov 2017 *)

(* ********** *)

Ltac unfold_tactic name :=
  intros;
  unfold name; (* fold name; *)
  reflexivity.
  
Require Import Arith List Bool.

(* ********** *)

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Fixpoint beq_list_nat (xs ys : list nat) : bool :=
  match xs with
    nil =>
    match ys with
      nil =>
      true
    | y :: ys' =>
      false
    end
  | x :: xs' =>
    match ys with
      nil =>
      false
    | y :: ys' =>
      (x =n= y) && beq_list_nat xs' ys'
    end
  end.

Notation "A =ns= B" :=
  (beq_list_nat A B) (at level 70, right associativity).

(* ********** *)

Lemma binomial_expansion :
  forall x y : nat,
    (x + y) * (x + y) =
    x * x + 2 * x * y + y * y.
Proof.
  intros x y.
  ring.
Qed.

Definition binomial_expansion_Sn :
  forall n : nat,
    (S n) * (S n) =
    S (2 * n) + n * n.
Proof.
  intro n.
  apply (binomial_expansion 1 n).
Qed.

(* ********** *)

CoInductive Stream (T : Type) : Type :=
| Cons : T -> Stream T -> Stream T.

Check Cons.

CoInductive bisimilar_Stream (T : Type) (eq_T : T -> T -> Prop) : Stream T -> Stream T -> Prop :=
| Bisimilar :
    forall (x1 x2 : T)
           (x1s x2s : Stream T),
    eq_T x1 x2 ->
    bisimilar_Stream T eq_T x1s x2s ->
    bisimilar_Stream T eq_T (Cons T x1 x1s) (Cons T x2 x2s).

(* ********** *)

(* Reasoning with streams: *)

Definition decompose_Stream (T : Type) (xs : Stream T) :=
  match xs with
    | Cons _ x xs' =>
      Cons T x xs'
  end.

Lemma unfold_decompose_Stream :
  forall (T : Type)
         (x : T)
         (xs' : Stream T),
    decompose_Stream T (Cons T x xs') =
    Cons T x xs'.
Proof.
  unfold_tactic decompose_Stream.
Qed.

Theorem decomposition_Stream :
  forall (T : Type)
         (xs : Stream T),
    xs =
    decompose_Stream T xs.
Proof.
  intros T [x xs'].
  rewrite -> unfold_decompose_Stream.
  reflexivity.
Qed.

(* ********** *)

(* "prefix n xs" maps the stream xs into the list of its n first elements *)

Fixpoint prefix (T : Type) (xs : Stream T) (n : nat) : list T :=
  match n with
    | 0 =>
      nil
    | S n' =>
      match xs with
      | Cons _ x xs' =>
        x :: (prefix T xs' n')
      end
  end.

Lemma unfold_prefix_O :
  forall (T : Type)
         (xs : Stream T),
    prefix T xs 0 =
    nil.
Proof.
  unfold_tactic prefix.
Qed.

Lemma unfold_prefix_S :
  forall (T : Type)
         (x : T)
         (xs' : Stream T)
         (n' : nat),
    prefix T (Cons T x xs') (S n') =
    x :: (prefix T xs' n').
Proof.
  unfold_tactic prefix.
Qed.

(* ********** *)

(* "partial_sums ns" maps a stream of natural numbers to the stream of its partial sums *)

CoFixpoint partial_sums_aux (a : nat) (ns : Stream nat) : Stream nat :=
  match ns with
    | Cons _ n ns' =>
      Cons nat (n + a) (partial_sums_aux (n + a) ns')
  end.

Lemma unfold_partial_sums_aux :
  forall (a n : nat)
         (ns' : Stream nat),
    partial_sums_aux a (Cons nat n ns') =
    Cons nat (n + a) (partial_sums_aux (n + a) ns').
Proof.
  intros a n ns'.
  rewrite -> (decomposition_Stream
                nat
                (partial_sums_aux a (Cons nat n ns'))).
  unfold_tactic partial_sums_aux.
Qed.

Definition partial_sums ns := partial_sums_aux 0 ns.

(* ********** *)

CoFixpoint zeroes : Stream nat :=
  Cons nat 0 zeroes.

Definition test_zeroes (s : Stream nat) :=
  ((prefix nat s 5) =ns=
   0 :: 0 :: 0 :: 0 :: 0 :: nil).
     
Compute (test_zeroes zeroes).

Lemma unfold_zeroes :
  zeroes = Cons nat 0 zeroes.
Proof.
  rewrite -> (decomposition_Stream nat zeroes) at 1.
  unfold decompose_Stream.
  unfold_tactic zeroes.
Qed.

(* ********** *)

CoFixpoint ones : Stream nat :=
  Cons nat 1 ones.

(*
Compute prefix 3 ones.
     = 1 :: 1 :: 1 :: nil
     : list nat
*)

Definition test_ones (s : Stream nat) :=
  ((prefix nat s 5) =ns=
   1 :: 1 :: 1 :: 1 :: 1 :: nil).
     
Compute (test_ones ones).

Lemma unfold_ones :
  ones = Cons nat 1 ones.
Proof.
  rewrite -> (decomposition_Stream nat ones) at 1.
  unfold decompose_Stream.
  unfold_tactic ones.
Qed.

(* ***** *)

Definition ones' : Stream nat :=
  partial_sums (Cons nat 1 zeroes).

Compute (test_ones ones').

(* ***** *)

Theorem the_same_ones :
  bisimilar_Stream nat eq_nat ones ones'.
Proof.
  unfold ones'.
  unfold partial_sums.
  rewrite -> unfold_partial_sums_aux.
  rewrite -> Nat.add_0_r.
  cofix coIH.

  rewrite -> unfold_ones.
  rewrite -> unfold_zeroes.
  rewrite -> unfold_partial_sums_aux.
  rewrite -> Nat.add_0_l.
  
  Check (Bisimilar nat eq_nat).
  Check (Bisimilar nat eq_nat 1 1 ones (Cons nat 1 (partial_sums_aux 1 zeroes)) (eq_nat_refl 1)).
  exact (Bisimilar nat eq_nat 1 1 ones (Cons nat 1 (partial_sums_aux 1 zeroes)) (eq_nat_refl 1) coIH).
Qed.  

(* ********** *)

CoFixpoint zero_one_s : Stream nat :=
  Cons nat 0 (Cons nat 1 zero_one_s).

Definition test_zero_one_s (s : Stream nat) :=
  ((prefix nat s 5) =ns=
   0 :: 1 :: 0 :: 1 :: 0 :: nil).
     
Compute (test_zero_one_s zero_one_s).

Lemma unfold_zero_one_s :
  zero_one_s = Cons nat 0 (Cons nat 1 zero_one_s).
Proof.
  rewrite -> (decomposition_Stream nat zero_one_s) at 1.
  rewrite -> (decomposition_Stream nat zero_one_s) at 1.
  unfold decompose_Stream.
  unfold_tactic zero_one_s.
Qed.

(* ***** *)

CoFixpoint one_zero_s : Stream nat :=
  Cons nat 1 (Cons nat 0 one_zero_s).

Definition test_one_zero_s (s : Stream nat) :=
  ((prefix nat s 5) =ns=
   1 :: 0 :: 1 :: 0 :: 1 :: nil).
     
Compute (test_one_zero_s one_zero_s).

Lemma unfold_one_zero_s :
  one_zero_s = Cons nat 1 (Cons nat 0 one_zero_s).
Proof.
  rewrite -> (decomposition_Stream nat one_zero_s) at 1.
  rewrite -> (decomposition_Stream nat one_zero_s) at 1.
  unfold decompose_Stream.
  unfold_tactic one_zero_s.
Qed.

(* ***** *)

Theorem the_same_zero_one_s :
  bisimilar_Stream nat eq_nat zero_one_s (Cons nat 0 one_zero_s).
Proof.
  cofix coIH.
  rewrite -> unfold_zero_one_s.
  rewrite -> unfold_one_zero_s.
  
  Check (Bisimilar nat eq_nat).
  Check (Bisimilar nat eq_nat 1 1 zero_one_s (Cons nat 0 one_zero_s) (eq_nat_refl 1) coIH).
  assert (inner_bisimilarity:= (Bisimilar nat eq_nat 1 1 zero_one_s (Cons nat 0 one_zero_s) (eq_nat_refl 1) coIH)).
  Check (Bisimilar nat eq_nat 0 0 (Cons nat 1 zero_one_s) (Cons nat 1 (Cons nat 0 one_zero_s)) (eq_nat_refl 0) inner_bisimilarity).
  exact (Bisimilar nat eq_nat 0 0 (Cons nat 1 zero_one_s) (Cons nat 1 (Cons nat 0 one_zero_s)) (eq_nat_refl 0) inner_bisimilarity).
Qed.

(*step by step*)
Theorem the_same_one_zero_s'' :
  bisimilar_Stream nat eq_nat one_zero_s (Cons nat 1 zero_one_s).
Proof.
  cofix coIH.
  rewrite -> unfold_zero_one_s.
  rewrite -> unfold_one_zero_s.

  apply Bisimilar.
  apply (eq_nat_refl 0).
  apply Bisimilar.
  apply (eq_nat_refl 0).
  exact coIH.  
Qed.
(*with assert statement *)
Theorem the_same_one_zero_s :
  bisimilar_Stream nat eq_nat one_zero_s (Cons nat 1 zero_one_s).

Proof.
  cofix coIH.
  rewrite -> unfold_zero_one_s.
  rewrite -> unfold_one_zero_s.
  
  Check (Bisimilar nat eq_nat).
  Check (Bisimilar nat eq_nat 0 0 one_zero_s (Cons nat 1 zero_one_s) (eq_nat_refl 0) coIH).
  assert (inner_bisimilarity:= (Bisimilar nat eq_nat 0 0 one_zero_s (Cons nat 1 zero_one_s) (eq_nat_refl 0) coIH)).
  Check (Bisimilar nat eq_nat 1 1 (Cons nat 0 one_zero_s)  (Cons nat 0 (Cons nat 1 zero_one_s)) (eq_nat_refl 1) inner_bisimilarity).
  exact (Bisimilar nat eq_nat 1 1 (Cons nat 0 one_zero_s)  (Cons nat 0 (Cons nat 1 zero_one_s)) (eq_nat_refl 1) inner_bisimilarity).
Qed.

(*with apply tactic*)
Theorem the_same_one_zero_s''' :
  bisimilar_Stream nat eq_nat one_zero_s (Cons nat 1 zero_one_s).

Proof.
  cofix coIH.
  rewrite -> unfold_zero_one_s.
  rewrite -> unfold_one_zero_s.
  (*do it outside-in*)
  Abort.
 
(*in one statement*)
Theorem the_same_one_zero_s' :
  bisimilar_Stream nat eq_nat one_zero_s (Cons nat 1 zero_one_s).
Proof.
  cofix coIH.
  rewrite -> unfold_zero_one_s.
  rewrite -> unfold_one_zero_s.  
  exact (Bisimilar nat eq_nat 1 1 (Cons nat 0 one_zero_s)  (Cons nat 0 (Cons nat 1 zero_one_s)) (eq_nat_refl 1) (Bisimilar nat eq_nat 0 0 one_zero_s (Cons nat 1 zero_one_s) (eq_nat_refl 0) coIH)).
Qed.
(* ********** *)

CoFixpoint make_successive_numbers (i : nat) : Stream nat :=
  Cons nat i (make_successive_numbers (S i)).

Definition test_successive_numbers (candidate : nat -> Stream nat) :=
  ((prefix nat (candidate 5) 6) =ns=
   5 :: 6 :: 7 :: 8 :: 9 :: 10 :: nil).
     
Compute (test_successive_numbers make_successive_numbers).

Lemma unfold_make_successive_numbers :
  forall i : nat,
    make_successive_numbers i =
    Cons nat i (make_successive_numbers (S i)).
Proof.
  intro i.
  rewrite -> (decomposition_Stream nat (make_successive_numbers i)).
  unfold decompose_Stream.
  unfold_tactic make_successive_numbers.
Qed.

Definition test_successive_positive_numbers (s : Stream nat) :=
  ((prefix nat s 6) =ns=
   1 :: 2 :: 3 :: 4 :: 5 :: 6 :: nil).
     
Definition successive_positive_numbers :=
  make_successive_numbers 1.

Compute (test_successive_positive_numbers successive_positive_numbers).

(* ***** *)

Definition successive_positive_numbers' :=
  partial_sums ones.

Compute (test_successive_positive_numbers successive_positive_numbers').

(* ***** *)
Theorem the_same_successive_positive_numbers :
  bisimilar_Stream
    nat
    eq_nat
    successive_positive_numbers
    successive_positive_numbers'.
Proof.
  unfold successive_positive_numbers.
  unfold successive_positive_numbers'.
  unfold partial_sums.
  cofix coIH.
  
  rewrite -> unfold_make_successive_numbers.
  rewrite -> unfold_ones.
  rewrite -> unfold_partial_sums_aux.
  rewrite -> Nat.add_0_r.
  Check (Bisimilar nat eq_nat 1 1 (make_successive_numbers 2) (partial_sums_aux 1 ones) (eq_nat_refl 1)).
  apply (Bisimilar nat eq_nat 1 1 (make_successive_numbers 2) (partial_sums_aux 1 ones) (eq_nat_refl 1)).
  
  rewrite -> unfold_make_successive_numbers.
  rewrite -> unfold_ones.
  rewrite -> unfold_partial_sums_aux.
  rewrite ->2 Nat.add_1_l at 1.
  Check (Bisimilar nat eq_nat 2 2 (make_successive_numbers 3) (partial_sums_aux 2 ones) (eq_nat_refl 1)).
Abort.


Lemma the_same_successive_positive_numbers_aux:
  forall i : nat,
    bisimilar_Stream
      nat
      eq_nat 
      (make_successive_numbers (S i))
      (partial_sums_aux i ones).
Proof.
  cofix coIH.
  intro i.
  rewrite -> unfold_make_successive_numbers.
  rewrite -> unfold_ones.
  rewrite -> unfold_partial_sums_aux.
  simpl (1 + i).
  (*rewrite ->2 Nat.add_1_l at 1.*)
  Check (Bisimilar nat eq_nat (S i) (S i) (make_successive_numbers (S (S i))) (partial_sums_aux (S i) ones) (eq_nat_refl (S i)) (coIH (S i))).
  exact (Bisimilar nat eq_nat (S i) (S i) (make_successive_numbers (S (S i))) (partial_sums_aux (S i) ones) (eq_nat_refl (S i)) (coIH (S i))).
Qed.

Theorem the_same_successive_positive_numbers :
  bisimilar_Stream
    nat
    eq_nat
    successive_positive_numbers
    successive_positive_numbers'.
Proof.
  unfold successive_positive_numbers.
  unfold successive_positive_numbers'.
  unfold partial_sums.
  cofix coIH.
  exact (the_same_successive_positive_numbers_aux 0).
Qed.    
(* ********** *)

(* end of week-14_streams.v *)

