(* week-05_consec_even.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 05 Sep 2017 *)

(* ********** *)

(* Paraphernalia: *)
Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).


(* ********** *)


Definition test_evenp (candidate : nat -> bool) : bool :=
  (eqb (candidate 0) true)
  &&
  (eqb (candidate 1) false)
  &&
  (eqb (candidate 7) false)
  &&
  (eqb (candidate 8) true)
  &&
  (eqb (candidate 17) false)
  .

Fixpoint evenp (n : nat) : bool :=
  match n with
  | 0 => true
  | S n' => negb (evenp n')
  end.

  Compute (test_evenp evenp).
  
  Lemma sum_even_even_is_even (a b : nat) :
    evenp(a) = true -> evenp(b) = true -> evenp(a + b) = true.
    Admitted.
    
Theorem consec_is_even :
  forall n: nat,
   evenp(n * S n) = true. 

  intro n.
  induction n as [ | n' IHn'].
  Search (0 * _ = _).
  rewrite (Nat.mul_0_l 1).
  unfold evenp.
  reflexivity.

  Check Nat.add_1_l n'.
  rewrite <- (Nat.add_1_l n').
  rewrite <- (Nat.add_1_l (1 + n')).

  Search (_ + (_ + _) = _).
  Check (Nat.add_assoc 1 1 n').
  rewrite -> (Nat.add_assoc 1 1 n').
  
  Search (_ * _ = _ + _).
  Check (Nat.mul_add_distr_l (1 + n') (1 + 1) (n')).
  rewrite -> (Nat.mul_add_distr_l (1 + n') (1 + 1) (n')).

  Check (sum_even_even_is_even ((1 + n') * (1 + 1)) ((1 + n') * n')).
  apply sum_even_even_is_even.
  Check (Nat.add_1_l 1).
  rewrite -> (Nat.add_1_l 1).

  Restart.

  Fixpoint evenp (n : nat) : bool :=
  match n with
  | 0 => true
  | S n' => negb (evenp n')
  end.

  Compute (test_evenp evenp).
  
  
  (* ********** *)

(* end of week-05_consec_even.v *)