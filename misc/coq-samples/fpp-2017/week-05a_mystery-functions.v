(* week-05a_mystery-functions.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 12 Sep 2017 *)

(* ********** *)

(* Your name and e-mail address: ... *)

(* ***********)

(* Paraphernalia: *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Definition beq_nat_nat A B :=
  match A, B with
    (a1, b1), (a2, b2) =>
    (a1 =n= a2) && (b1 =n= b2)
  end.
                           

Notation "A =nn= B" :=
  (beq_nat_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* ********** *)

Definition specification_of_mystery_function_00 (mf : nat -> nat) :=
  (mf 0 = 1)
  /\
  (forall i j : nat,
    mf (S (i + j)) = mf i + mf j).

(* ***** *)

Theorem there_is_at_most_one_mystery_function_00 :
  forall f g : nat -> nat,
    specification_of_mystery_function_00 f ->
    specification_of_mystery_function_00 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_00.
  intros [S_f_0 S_f_S] [S_g_0 S_g_S].
  intro n.
  induction n as [ | n' IHn'].

  rewrite -> S_g_0.
  apply S_f_0.

  Search ( _ + 0 = _).
  rewrite <- (Nat.add_0_r n').
  rewrite -> (S_f_S n' 0).
  rewrite -> (S_g_S n' 0).
  rewrite -> S_f_0.
  rewrite <- S_g_0.
  rewrite -> IHn'.
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

(* ***** *)

(* Flesh out the following unit test
   as you tabulate mystery_function_00:
*)
Definition unit_test_for_mystery_function_00 (mf : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (mf 0 =n= 1)
(*
   mf 1
   = mf (S (0 + 0)) = mf 0 + mf 0 = 1 + 1 = 2
*)
  &&
  (mf 1 =n= 2)
  &&
  (mf 2 =n= 3)
  &&
  (mf 3 =n= 4)
  .


Definition mystery_function_00 := S.

Compute unit_test_for_mystery_function_00 mystery_function_00.

Theorem there_is_at_least_one_mystery_function_00 :
  specification_of_mystery_function_00 mystery_function_00.
Proof.
  unfold mystery_function_00.
  unfold specification_of_mystery_function_00.
  split.
  reflexivity.

  Search (S _ + _ = _).
  intros i j.
  rewrite <- (plus_Sn_m i j).
  rewrite -> (plus_Snm_nSm i j).
  rewrite -> (plus_Sn_m i (S j)).
  reflexivity.
Qed.
(* ********** *)

Definition specification_of_mystery_function_01 (mf : nat -> nat) :=
  (mf 0 = 0)
  /\
  (forall i j : nat,
    mf (i + S j) = mf i + S (mf j)).

(* ***** *)

Proposition there_is_at_most_one_mystery_function_01 :
  forall f g : nat -> nat,
    specification_of_mystery_function_01 f ->
    specification_of_mystery_function_01 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_01.
  intros [S_f_0 S_f_S] [S_g_0 S_g_S].
  intro n.
  induction n as [ | n' IHn'].

  rewrite -> S_g_0.
  apply S_f_0.

  rewrite <- (Nat.add_0_l (S n')).
  Check (S_f_S 0 n').
  rewrite -> (S_f_S 0 n').
  rewrite -> (S_g_S 0 n').
  rewrite -> S_f_0.
  rewrite -> S_g_0.
  rewrite -> IHn'.
  reflexivity.
Qed.  
(* ***** *)

(* Flesh out the following unit test
   as you tabulate mystery_function_01:
*)
Definition unit_test_for_mystery_function_1 (mf : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (mf 0 =n= 0)
(*
   mf 1
   = ...
*)
  &&
  (mf 1 =n= 1)
  &&
  (mf 2 =n= 2)
  .


Definition mystery_function_01 := (fun n: nat => n).
  
Compute unit_test_for_mystery_function_1 mystery_function_01.

Theorem there_is_at_least_one_mystery_function_01 :
  specification_of_mystery_function_01 mystery_function_01.
Proof.
  unfold mystery_function_01.
  unfold specification_of_mystery_function_01.
  split.
  reflexivity.

  intros i j.
  reflexivity.
Qed.

(* ********** *)
Definition specification_of_mystery_function_02 (mf_a : nat -> nat) :=
  (mf_a 0 = 0)
  /\
  (forall n' : nat,
    mf_a (S n') = mf_a n' + S (2 * n')).

Definition unit_test_for_mystery_function_02 (mf : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (mf 0 =n= 0)
(*
   mf 1
   = ...
*)
  &&
  (mf 1 =n= 1)
  &&
  (mf 2 =n= 4)
  &&
  (mf 3 =n= 9)
  &&
  (mf 4 =n= 16)
  
.


Definition mystery_function_02 := (fun n: nat => n * n).
  
Compute unit_test_for_mystery_function_02 mystery_function_02.

Lemma plus_1_l:
  forall n: nat,
    1+n = S n.
Admitted.
Theorem there_is_at_least_one_mystery_function_02 :
  specification_of_mystery_function_02 mystery_function_02.
Proof.
  unfold mystery_function_02.
  unfold specification_of_mystery_function_02.
  split.

  Search (0 * _ = 0).
  apply Nat.mul_0_l.

  intro n'.
  rewrite <- (plus_1_l n').
  Search (_ * (_ + _) = _).
  rewrite -> (Nat.mul_add_distr_l (1 + n') 1 n').
  Check Nat.mul_add_distr_r.
  rewrite -> (Nat.mul_add_distr_r 1 n' 1).
  rewrite -> (Nat.mul_add_distr_r 1 n' n').
  Search (1+ _ = _).
  rewrite -> (Nat.mul_1_l 1).
  rewrite -> (Nat.mul_1_r n').
  rewrite -> (Nat.mul_1_l n').
  rewrite <- (plus_1_l (2 * n')).
  Check (plus_comm (n' * n') (1 + 2 * n')).
  rewrite -> (plus_comm (n' * n') (1 + 2 * n')).

  Search (S _ * _ = _).
  rewrite -> (Nat.mul_succ_l 1 n').
  rewrite -> (Nat.mul_1_l n').
  Check plus_assoc.
  rewrite -> (plus_assoc (1 + n') _ _).
  Check plus_assoc 1 n' n'.
  rewrite -> (plus_assoc 1 n' n'). 
  reflexivity.
  
Qed.


(* ********** *)

Definition specification_of_mystery_function_03 (mf : nat -> nat -> nat) :=
  (mf 0 0 = 0)
  /\
  (forall i j: nat,
      mf (S i) j = S (mf i j))
  /\
  (forall i j: nat,
      S (mf i j) = mf i (S j)).

Definition unit_test_for_mystery_function_03 (mf : nat -> nat -> nat) :=
(*
   mf 0 0 = 0 /\
   mf 1 0 = S (mf 0 0) = mf 0 1 
*)
  (mf 0 0 =n= 0)
  &&
  (mf 1 0 =n= 1)
  &&
  (mf 0 1 =n= 1)
(*
   mf 2 1 
   = S (mf 1 1) 
   = mf 1 2  
*)
  &&
  (mf 1 1 =n= 2)
  &&
  (mf 2 1 =n= 3)
  &&
  (mf 1 2 =n= 3)
  &&
  (mf 2 2 =n= 4)
  &&
  (mf 2 3 =n= 5)
.

Definition mystery_function_03 := (fun n m: nat => n + m).
  
Compute unit_test_for_mystery_function_03 mystery_function_03.

Theorem there_is_at_least_one_mystery_function_03 :
  specification_of_mystery_function_03 mystery_function_03.
Proof.
  unfold mystery_function_03.
  unfold specification_of_mystery_function_03.
  split. 
  Search (0 + _ = _).
  rewrite -> (Nat.add_0_l 0).
  reflexivity.

  split.
  intros i j.
  Search (S _ + _ = _).
  Check (plus_Sn_m i j).
  apply (plus_Sn_m i j).

  intros i j.
  Search (S _ + _ = _ + S _).
  apply (plus_Snm_nSm i j).
Qed.
(* ********** *)


Definition specification_of_mystery_function_04 (mf : nat -> nat * nat) :=
  (mf 0 = (1, 0))
  /\
  (forall n' : nat,
    mf (S n') = let (x, y) := mf n'
               in (x + y, x)).

Definition unit_test_for_mystery_function_04 (mf : nat -> nat * nat) :=
(*
   The following equality is in the specification:
*)
  (mf 0 =nn= (1, 0))

.


(* ********** *)







Definition specification_of_mystery_function_05 (f : nat -> nat * nat) :=
  (f 0 = (0, 1))
  /\
  (forall n' : nat,
    f (S n') = let (x, y) := f n'
               in (S x, y * S x)).

(* ***********)

(* end of week-05a_mystery-functions.v *)
