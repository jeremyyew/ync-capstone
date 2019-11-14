(* week-04b_specifications-aftermath.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Fri 09 Sep 2017 after the lecture *)

(* ********** *)

(* Standard paraphernalia: *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Specification: *)

Definition specification_of_the_factorial_function (fac : nat -> nat) :=
  (fac 0 = 1)
  /\
  (forall n' : nat,
      fac (S n') = (S n') * fac n').

(* ***** *)

(* Unit-test function: *)

Definition test_fac (candidate: nat -> nat) : bool :=
  (candidate 0 =n= 1)
  && 
  (candidate 1 =n= 1)
  && 
  (candidate 2 =n= 2) 
  && 
  (candidate 3 =n= 6)
  && 
  (candidate 4 =n= 24) 
  && 
  (candidate 5 =n= 120)
  .

(* ***** *)

(* Property of the specification: *)

Proposition there_is_at_most_one_factorial_function :
  forall f g : nat -> nat,
    (specification_of_the_factorial_function f) ->
    (specification_of_the_factorial_function g) ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_factorial_function.
  intros [S_f_0 S_f_S] [S_g_0 S_g_S].
  intro n.
  induction n as [ | n' IH_n'].

  rewrite -> S_f_0.
  rewrite -> S_g_0.
  reflexivity.

  rewrite -> (S_f_S n').
  rewrite -> (S_g_S n').
  rewrite -> IH_n'.
  reflexivity.
Qed.

(* ***** *)

(* Soundness of the unit tests: *)

Proposition soundness_of_test_fac :
  forall fac : nat -> nat,
    specification_of_the_factorial_function fac ->
    test_fac fac = true.
Proof.
Abort.

(* ***** *)

(* Canonical implementation of the factorial function in direct style: *)

Fixpoint fac_v0 (n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    (S n') * (fac_v0 n')
  end.

(* Sanity check: *)

Compute (test_fac fac_v0).

(* The standard mandatory unfold lemmas: *)

Lemma unfold_fac_v0_O :
  fac_v0 0 = 1.
Proof.
  unfold_tactic fac_v0.
Qed.

Lemma unfold_fac_v0_S :
  forall n' : nat,
    fac_v0 (S n') = (S n') * (fac_v0 n').
Proof.
  unfold_tactic fac_v0.
Qed.

(* fac_v0 satisfies the specification of the factorial function: *)

Proposition there_is_at_least_one_factorial_function_namely_fac_v0 :
  specification_of_the_factorial_function fac_v0.
Proof.
  unfold specification_of_the_factorial_function.
  split.

  apply unfold_fac_v0_O.

  apply unfold_fac_v0_S.
Qed.

(* ***** *)

(* Implementation of the auxiliary function in accumulator-passing style
   for the factorial function: *)

Fixpoint fac_v1_aux (n a : nat) : nat :=
  match n with
  | O =>
    a
  | S n' =>
    fac_v1_aux n' ((S n') * a)
  end.

(* The standard mandatory unfold lemmas: *)

Lemma unfold_fac_v1_aux_O :
  forall a : nat,
    fac_v1_aux O a = a.
Proof.
  unfold_tactic fac_v1_aux.
Qed.

Lemma unfold_fac_v1_aux_S :
  forall n' a : nat,
    fac_v1_aux (S n') a = fac_v1_aux n' ((S n') * a).
Proof.
  unfold_tactic fac_v1_aux.
Qed.

(* Implementation of the factorial function with an accumulator: *)

Definition fac_v1 (n : nat) : nat :=
  fac_v1_aux n 1.

(* Sanity check: *)

Compute (test_fac fac_v1).

(* Master lemma (eureka): *)

Lemma about_fac_v1_aux :
  forall n a : nat,
    fac_v1_aux n a = a * (fac_v1_aux n 1).
Proof.
  intro n.
  induction n as [ | n' IH_n'].

  intro a.
  Check (unfold_fac_v1_aux_O a).
  rewrite -> (unfold_fac_v1_aux_O a).
  Check (unfold_fac_v1_aux_O 1).
  rewrite -> (unfold_fac_v1_aux_O 1).
  Check (Nat.mul_1_r a).
  rewrite -> (Nat.mul_1_r a).
  reflexivity.

  intro a.
  Check (unfold_fac_v1_aux_S n' a).
  rewrite -> (unfold_fac_v1_aux_S n' a).
  Check (IH_n' (S n' * a)).
  rewrite -> (IH_n' (S n' * a)).
  Check (unfold_fac_v1_aux_S n' 1).
  rewrite -> (unfold_fac_v1_aux_S n' 1).
  rewrite -> (Nat.mul_1_r (S n')).
  Check (IH_n' (S n')).
  rewrite -> (IH_n' (S n')).
  Check mult_assoc.
  Check (mult_assoc a (S n') (fac_v1_aux n' 1)).
  rewrite -> (mult_assoc a (S n') (fac_v1_aux n' 1)).
  Check mult_comm.
  rewrite -> (mult_comm (S n') a).
  reflexivity.
Qed.

Proposition there_is_at_least_one_factorial_function_fac_v1 :
  specification_of_the_factorial_function fac_v1.
Proof.
  unfold fac_v1.
  unfold specification_of_the_factorial_function.
  split.

  Check (unfold_fac_v1_aux_O 1).
  apply (unfold_fac_v1_aux_O 1).

  intro n'.
  Check (unfold_fac_v1_aux_S n' 1).
  rewrite -> (unfold_fac_v1_aux_S n' 1).
  Search (_ * 1 = _).
  Check (Nat.mul_1_r (S n')).
  rewrite -> (Nat.mul_1_r (S n')).
  (* and we are stuck *)
  (* so we devise the master lemma above *)
  Check (about_fac_v1_aux n' (S n')).
  apply (about_fac_v1_aux n' (S n')).
Qed.

(* More perspicuous master lemma (eureka): *)

Lemma about_fac_v1_aux' :
  forall n a1 a2 : nat,
    fac_v1_aux n (a1 * a2) = a2 * (fac_v1_aux n a1).
Proof.
  intro n.
  induction n as [ | n' IH_n'].

  intros a1 a2.
  Check (unfold_fac_v1_aux_O (a1 * a2)).
  rewrite -> (unfold_fac_v1_aux_O (a1 * a2)).
  Check (unfold_fac_v1_aux_O a1).
  rewrite -> (unfold_fac_v1_aux_O a1).
  Check (mult_comm a1 a2).
  apply (mult_comm a1 a2).

  intros a1 a2.
  Check (unfold_fac_v1_aux_S n' (a1 * a2)).
  rewrite -> (unfold_fac_v1_aux_S n' (a1 * a2)).
  Check (unfold_fac_v1_aux_S n' a1).
  rewrite -> (unfold_fac_v1_aux_S n' a1).
  Check mult_assoc.
  Check (mult_assoc (S n') a1 a2).
  rewrite -> (mult_assoc (S n') a1 a2).
  Check (IH_n' (S n' * a1) a2).
  apply (IH_n' (S n' * a1) a2).
Qed.

Proposition there_is_at_least_one_factorial_function_namely_fac_v1' :
  specification_of_the_factorial_function fac_v1.
Proof.
  unfold fac_v1.
  unfold specification_of_the_factorial_function.
  split.

  Check (unfold_fac_v1_aux_O 1).
  apply (unfold_fac_v1_aux_O 1).

  intro n'.
  Check (unfold_fac_v1_aux_S n' 1).
  rewrite -> (unfold_fac_v1_aux_S n' 1).
  rewrite -> (mult_comm (S n') 1).
  Check (about_fac_v1_aux' n' 1 (S n')).
  apply (about_fac_v1_aux' n' 1 (S n')).
Qed.

(* Alternative perspicuous master lemma (eureka): *)

Lemma about_fac_v1_aux'' :
  forall n a1 a2 : nat,
    fac_v1_aux n (a1 * a2) = a1 * (fac_v1_aux n a2).
Proof.
  intro n.
  induction n as [ | n' IH_n'].

  intros a1 a2.
  Check (unfold_fac_v1_aux_O (a1 * a2)).
  rewrite -> (unfold_fac_v1_aux_O (a1 * a2)).
  Check (unfold_fac_v1_aux_O a2).
  rewrite -> (unfold_fac_v1_aux_O a2).
  reflexivity.

  intros a1 a2.
  Check (unfold_fac_v1_aux_S n' (a1 * a2)).
  rewrite -> (unfold_fac_v1_aux_S n' (a1 * a2)).
  Check (unfold_fac_v1_aux_S n' a2).
  rewrite -> (unfold_fac_v1_aux_S n' a2).
  Check (IH_n' a1 (S n' * a2)).
  rewrite <- (IH_n' a1 (S n' * a2)).
  Check mult_assoc.
  Check (mult_assoc (S n') a1 a2).
  rewrite -> (mult_assoc (S n') a1 a2).
  Check (mult_assoc a1 (S n') a2).
  rewrite -> (mult_assoc a1 (S n') a2).
  Check mult_comm.
  Check (mult_comm (S n') a1).
  rewrite -> (mult_comm (S n') a1).
  reflexivity.
Qed.

Proposition there_is_at_least_one_factorial_function_namely_fac_v1'' :
  specification_of_the_factorial_function fac_v1.
Proof.
  unfold fac_v1.
  unfold specification_of_the_factorial_function.
  split.

  Check (unfold_fac_v1_aux_O 1).
  apply (unfold_fac_v1_aux_O 1).

  intro n'.
  Check (unfold_fac_v1_aux_S n' 1).
  rewrite -> (unfold_fac_v1_aux_S n' 1).
  Check (about_fac_v1_aux'' n' (S n') 1).
  apply (about_fac_v1_aux'' n' (S n') 1).
Qed.

(* ********** *)

(* Specification: *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  (fib 0 = 0)
  /\
  (fib 1 = 1)
  /\
  (forall n'' : nat,
      fib (S (S n'')) = fib (S n'') + fib n'').

(* ***** *)

(* Unit-test function: *)

Definition test_fib (candidate: nat -> nat) : bool :=
  (candidate 0 =n= 0)
  && 
  (candidate 1 =n= 1)
  && 
  (candidate 2 =n= 1)
  && 
  (candidate 3 =n= 2)
  && 
  (candidate 4 =n= 3)
  && 
  (candidate 5 =n= 5)
  && 
  (candidate 6 =n= 8)
  && 
  (candidate 7 =n= 13)
  && 
  (candidate 8 =n= 21)
  .

(* ***** *)

(* Property of the specification: *)

Proposition there_is_at_most_one_fibonacci_function :
  forall f g : nat -> nat,
    (specification_of_the_fibonacci_function f) ->
    (specification_of_the_fibonacci_function g) ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_fibonacci_function.
  intros [S_f_0 [S_f_1 S_f_SS]].
  intros [S_g_0 [S_g_1 S_g_SS]].

  Restart.

  intros f g.
  intros S_f S_g.
  intro n.

  induction n as [ | [ | n''] IH_n''].

  unfold specification_of_the_fibonacci_function in S_f.
  destruct S_f as [S_f_0 _].
  unfold specification_of_the_fibonacci_function in S_g.
  destruct S_g as [S_g_0 _].
  rewrite -> S_g_0.
  apply S_f_0.

  destruct S_f as [_ [S_f_1 _]].
  unfold specification_of_the_fibonacci_function in S_g.
  destruct S_g as [_ [S_g_1 _]].
  rewrite -> S_g_1.
  apply S_f_1.

  unfold specification_of_the_fibonacci_function in S_f.
  destruct S_f as [_ [_ S_f_SS]].
  unfold specification_of_the_fibonacci_function in S_g.
  destruct S_g as [_ [_ S_g_SS]].
  rewrite -> (S_f_SS n'').
  rewrite -> (S_g_SS n'').
  rewrite -> IH_n''.

  Restart.

  intros f g.
  unfold specification_of_the_fibonacci_function.
  intros [S_f_0 [S_f_1 S_f_SS]] [S_g_0 [S_g_1 S_g_SS]].
  assert (H_fib2 : forall n : nat,
             f n = g n /\ f (S n) = g (S n)).
    intro n.
    induction n as [ | n' [IH_n' IH_Sn']].

    rewrite -> S_g_0.
    rewrite -> S_g_1.
    split.
      apply S_f_0.
    apply S_f_1.

    split.
      apply IH_Sn'.
    rewrite -> (S_f_SS n').
    rewrite -> (S_g_SS n').
    rewrite -> IH_n'.
    rewrite -> IH_Sn'.
    reflexivity.

  intro n.
  Check (H_fib2 n).
  destruct (H_fib2 n) as [H_yay _].
  apply H_yay.
Qed.

(* ***** *)

(* Soundness of the unit tests: *)

Proposition soundness_of_test_fib :
  forall fib : nat -> nat,
    specification_of_the_fibonacci_function fib ->
    test_fib fib = true.
Proof.
Abort.

(* ***** *)

(* Canonical implementation of the fibonacci function in direct style: *)

Fixpoint fib_v0 (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => match n' with
            | O => 1
            | S n'' => (fib_v0 n') + (fib_v0 n'')
            end
  end.

(* Sanity check: *)

Compute (test_fib fib_v0).

(* The standard mandatory unfold lemmas: *)

Lemma unfold_fib_v0_O :
  fib_v0 O = 0.
Proof.
  unfold_tactic fib_v0.
Qed.

Lemma unfold_fib_v0_1 :
  fib_v0 1 = 1.
Proof.
  unfold_tactic fib_v0.
Qed.

Lemma unfold_fib_v0_SS :
  forall n'' : nat,
    fib_v0 (S (S n'')) = (fib_v0 (S n'')) + (fib_v0 n'').
Proof.
  unfold_tactic fib_v0.
Qed.

(* fib_v0 satisfies the specification of the fibonacci function: *)

Proposition there_is_at_least_one_fibonacci_function_namely_fib_v0 :
  specification_of_the_fibonacci_function fib_v0.
Proof.
  unfold specification_of_the_fibonacci_function.
  split.

  apply unfold_fib_v0_O.

  split.

  apply unfold_fib_v0_1.

  apply unfold_fib_v0_SS.
Qed.

(* ***** *)

(* Implementation of the auxiliary function in accumulator-passing style
   for the fibonacci function: *)

Fixpoint fib_v1_aux (n a1 a2 : nat) : nat :=
  match n with
  | 0 => a1
  | S n' => (fib_v1_aux n' a2 (a1 + a2))
  end.

(* The standard mandatory unfold lemmas: *)

(* ... *)

(* Implementation of the fib_v1 function with two accumulators: *)

Definition fib_v1 (n : nat) : nat :=
  fib_v1_aux n 0 1.

(* Sanity check: *)

Compute (test_fib fib_v1).

Proposition there_is_at_least_one_fibonacci_function_namely_fib_v1 :
  specification_of_the_fibonacci_function fib_v1.
Proof.
Abort.

(* ***** *)

(* Implementation of the auxiliary function in co-accumulator-receiving style
   for the fibonacci function: *)

Fixpoint fib_aux_v2 (n : nat) : nat * nat :=
  match n with
  | 0 => (0, 1)
  | S n' => match fib_aux_v2 n' with
              | (a1, a2) => (a2, a1 + a2)
            end
  end.

(* The standard mandatory unfold lemmas: *)

(* ... *)

(* Implementation of the fib_v2 function with two co-accumulators: *)

Definition fib_v2 (n : nat) : nat :=
  match fib_aux_v2 n with
    | (a1, a2) => a1
  end.

(* Sanity check: *)

Compute (test_fib fib_v2).

Proposition there_is_at_least_one_fibonacci_function_namely_fib_v2 :
  specification_of_the_fibonacci_function fib_v2.
Proof.
Abort.

(* ********** *)

(* end of week-04b_specifications-aftermath.v *)
