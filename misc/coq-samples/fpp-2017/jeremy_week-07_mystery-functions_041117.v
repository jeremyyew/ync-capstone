(* week-07_mystery-functions.v *)
(* Functional Programming and Proving (YSC3236) 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)

(* ********** *)
(*
   name:Jeremy Yew
   student ID number: A0156262H
   e-mail address: jeremy.yew@u.yale-nus.edu.sg
*)

(*
Edits as of 04 Nov 2017:
 - Completed mystery functions a to f. 
 - Re-wrote proofs for mystery functions k and l, inducting over targeted assert statements instead of general induction principles (commented out).  
 - Remaining: g, h, i, j.   
 *) 

(* ********** *)

(* Paraphernalia: *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).


(* ********** *)

Definition specification_of_the_mystery_function_a (mf : nat -> nat) :=
  (mf 0 = 1)
  /\
  (forall i j : nat,
    mf (S (i + j)) = 2 * mf i * mf j).

Definition unit_test_for_the_mystery_function_a (mf : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (mf 0 =n= 1)
  &&
  (*(mf (S (0 + 0) =n= 2 * mf (0) * mf (0))*)
  (mf 1 =n= 2)
  &&
  (*(mf (S (1 + 0) =n= 2 * mf (1) * mf (0))*)
  (mf 2 =n= 4)
  &&
  (*(mf (S (1 + 1) =n= 2 * mf (1) * mf (1)).*)
  (mf 3 =n= 8)
  &&
  (*(mf (S (2 + 1) =n= 2 * mf (2) * mf (1)).*)
  (mf 4 =n= 16)
  &&
  (mf 10 =n= 1024).

Fixpoint two_power_n (n : nat) : nat :=
  match n with
  |O =>
   1
  |S n' => 2 * (two_power_n n')
  end.
  
Compute unit_test_for_the_mystery_function_a two_power_n.

Lemma unfold_two_power_n_0:
  two_power_n 0 = 1.
Proof.
  unfold_tactic two_power_n.
Qed.

Lemma unfold_two_power_n_Sn':
  forall n' : nat,
  two_power_n (S n') = 2 * two_power_n n'.
Proof.
  unfold_tactic two_power_n.
Qed.

Proposition there_is_at_most_one_mystery_function_a :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_a f ->
    specification_of_the_mystery_function_a g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g. 
  unfold specification_of_the_mystery_function_a.
  intros [S_f_0 S_f_S] [S_g_0 S_g_S].
  induction n as [ | n' IHn'].
  rewrite -> S_f_0.
  rewrite -> S_g_0.
  reflexivity.

  rewrite <- (Nat.add_0_l n').
  rewrite -> S_f_S.
  rewrite -> S_g_S.
  rewrite -> IHn'.
  rewrite -> S_f_0.
  rewrite -> S_g_0.
  reflexivity.
Qed.

Lemma about_two_power_n:
  forall i j : nat,
    two_power_n (i + j) = two_power_n i * two_power_n j.
Proof.
  intros i.
  induction i as [ | i' IHi'].

  intro j.
  rewrite -> unfold_two_power_n_0.
  rewrite -> Nat.mul_1_l.
  rewrite -> Nat.add_0_l.
  reflexivity.

  intro j.
  rewrite <- (Nat.add_1_r i').
  rewrite <- (Nat.add_assoc i' 1 j).
  rewrite -> (Nat.add_1_l j).
  rewrite -> IHi'.

  rewrite -> (Nat.add_1_r i').
  rewrite ->2 (unfold_two_power_n_Sn').
  rewrite -> Nat.mul_comm.
  Check Nat.mul_assoc.
  rewrite <- Nat.mul_assoc.
  rewrite -> (Nat.mul_comm (two_power_n j) (two_power_n i')).
  rewrite -> Nat.mul_assoc.
  reflexivity.
Qed.
 
Lemma unfold_two_power_n_1:
  two_power_n 1 = 2.
Proof.
  unfold_tactic two_power_n.
Qed.
  
Theorem there_is_at_least_one_mystery_function_a :
  specification_of_the_mystery_function_a two_power_n.
Proof.
  unfold specification_of_the_mystery_function_a.
  split.
    rewrite -> unfold_two_power_n_0; reflexivity.
  intros i j.
  rewrite <- Nat.mul_assoc.  
  rewrite <- about_two_power_n.
  rewrite <- unfold_two_power_n_1.
  rewrite <- about_two_power_n.
  Check (Nat.add_1_l (i + j)).
  rewrite -> (Nat.add_1_l (i + j)).
  reflexivity.
Qed.
(* ********** *)

Definition specification_of_the_mystery_function_b (mf : nat -> nat) :=
  (mf 0 = 2)
  /\
  (forall i j : nat,
    mf (S (i + j)) = mf i * mf j).

Definition unit_test_for_the_mystery_function_b (mf : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (mf 0 =n= 2)
  &&
  (*(mf (S (0 + 0) =n= mf (0) * mf (0))*)
  (mf 1 =n= 4)
  &&
  (*(mf (S (1 + 0) =n= mf (1) * mf (0))*)
  (mf 2 =n= 8)
  &&
  (*(mf (S (1 + 1) =n= mf (1) * mf (1)).*)
  (mf 3 =n= 16)
  &&
  (*(mf (S (2 + 1) =n= mf (2) * mf (1)).*)
  (mf 4 =n= 32)
  &&
  (mf 10 =n= 2048).

Proposition there_is_at_most_one_mystery_function_b :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_b f ->
    specification_of_the_mystery_function_b g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g. 
  unfold specification_of_the_mystery_function_b.
  intros [S_f_0 S_f_S] [S_g_0 S_g_S].
  induction n as [ | n' IHn'].
  rewrite -> S_f_0.
  rewrite -> S_g_0.
  reflexivity.

  rewrite <- (Nat.add_0_l n').
  rewrite -> S_f_S.
  rewrite -> S_g_S.
  rewrite -> IHn'.
  rewrite -> S_f_0.
  rewrite -> S_g_0.
  reflexivity.
Qed.


Fixpoint two_power_Sn (n : nat) : nat :=
  match n with
  |O =>
   2
  |S n' => 2 * (two_power_Sn n')
  end.
  
Compute unit_test_for_the_mystery_function_b two_power_Sn.

Lemma unfold_two_power_Sn_0:
  two_power_Sn 0 = 2.
Proof.
  unfold_tactic two_power_Sn.
Qed.

Lemma unfold_two_power_Sn_Sn':
  forall n' : nat,
  two_power_Sn (S n') =  2 * (two_power_Sn n').
Proof.
  unfold_tactic two_power_Sn.
Qed.

Lemma about_two_power_Sn:
  forall i j : nat,
   2 * two_power_Sn (i + j) = two_power_Sn i * two_power_Sn j.
Proof.
  intros i.
  induction i as [ | i' IHi'].

  intro j.
  rewrite -> unfold_two_power_Sn_0.
  rewrite -> Nat.add_0_l.
  reflexivity.

  intro j.
  rewrite <- (Nat.add_1_r i').
  rewrite <- (Nat.add_assoc i' 1 j).
  rewrite -> IHi'.
  rewrite -> unfold_two_power_Sn_Sn'.
  rewrite -> Nat.mul_assoc.
  rewrite -> (Nat.mul_comm (two_power_Sn i') 2).  
  rewrite <- unfold_two_power_Sn_Sn'.
  rewrite -> (Nat.add_1_r i').
  reflexivity.
Qed.

Theorem there_is_at_least_one_mystery_function_b :
  specification_of_the_mystery_function_b two_power_Sn.
Proof.
  unfold specification_of_the_mystery_function_a.
  split.
    rewrite -> unfold_two_power_Sn_0; reflexivity.
  intros i j.
  rewrite <- about_two_power_Sn.
  rewrite <- unfold_two_power_Sn_Sn'.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_c (mf : nat -> nat -> nat) :=
  (forall j : nat,
      mf 0 j = j)
  /\
  (forall i : nat,
      mf i 0 = i)
  /\
  (forall i j k : nat,
      mf (i + k) (j + k) = (mf i j) + k).


Definition unit_test_for_the_mystery_function_c (mf : nat -> nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (mf 0 0 =n= 0)
  &&
  (mf 0 1 =n= 1)
  &&
  (mf 1 0 =n= 1)
  &&
  (*(mf (0 + 1) (0 + 1) =n= mf 0 0 + 1.*)
  (mf 1 1 =n= 1)
  &&
  (*(mf (0 + 1) (1 + 1) =n= mf 0 1 + 1.*)
  (mf 1 2 =n= 2)
  &&
  (*(mf (1 + 1) (0 + 1) =n= mf 1 0 + 1.*)
  (mf 2 1 =n= 2)
  &&
  (*(mf (1 + 1) (1 + 1) =n= mf 1 1 + 1.*)
  (mf 2 2 =n= 2)
  &&
  (*(mf (1 + 1) (2 + 1) =n= mf 1 2 + 1.*)
  (mf 2 3 =n= 3)
  &&
  (*(mf (1 + 1) (2 + 1) =n= mf 2 1 + 1.*)
  (mf 3 2 =n= 3)
    &&
  (*(mf (2 + 1) (2 + 1) =n= mf 2 2 + 1.*)
  (mf 3 3 =n= 3)
  &&
  (*(mf (2 + 1) (3 + 1) =n= mf 2 3 + 1.*)
  (mf 3 4 =n= 4).


Proposition there_is_at_most_one_mystery_function_c :
  forall f g : nat -> nat -> nat,
    specification_of_the_mystery_function_c f ->
    specification_of_the_mystery_function_c g ->
    forall l m : nat,
      f l m = g l m.
Proof.
  intros f g. 
  unfold specification_of_the_mystery_function_c.
  intros [S_f_0_l [S_f_0_r S_f_S]] [S_g_0_l [S_g_0_r S_g_S]].
  intro l.
  induction l as [ | l' IHl'].
  intro m.
  rewrite -> S_f_0_l.
  rewrite -> S_g_0_l.
  reflexivity.

  intro m.
  induction m as [ | m' IHm'].
  rewrite -> S_f_0_r.
  rewrite -> S_g_0_r.
  reflexivity.

  rewrite <- (Nat.add_1_r l').
  rewrite <- (Nat.add_1_r m').
  rewrite -> S_f_S.
  rewrite -> S_g_S.
  rewrite -> IHl'.
  reflexivity.
Qed.

Fixpoint max (a b : nat) : nat :=
  match a with
  | O =>
    b
  | S a' =>
    match b with
    | O =>
      a
    | S b' =>
      S (max a' b')
    end
  end.

Compute (unit_test_for_the_mystery_function_c max).
Lemma unfold_max_0_l :
  forall b : nat, 
  max 0 b = b.
Proof.
  unfold_tactic max.
Qed.

Lemma unfold_max_0_r :
  forall a : nat, 
  max a 0 = a.
Proof.
  intro a.
  induction a as [ | a' IHa'].
  rewrite -> unfold_max_0_l.
  reflexivity.
  unfold max.
  reflexivity.  
Qed.


Lemma unfold_max_S :
  forall a' b' : nat,
    max (S a') (S b') = S (max a' b').
Proof.
  unfold_tactic max.
Qed.

Theorem there_is_at_least_one_mystery_function_c :
  specification_of_the_mystery_function_c max.
Proof.
  unfold specification_of_the_mystery_function_c.
  split.
    exact unfold_max_0_l.
    split.
      exact unfold_max_0_r.
  intros i j k.
  induction k as [ | k' IHk'].
  
  rewrite ->3 Nat.add_0_r.
  reflexivity.
  
  rewrite <- (Nat.add_1_r k').
  rewrite ->2 Nat.add_assoc.
  rewrite ->2 Nat.add_1_r.
  rewrite -> unfold_max_S.
  rewrite -> IHk'.
  Search (S (_ + _) = _ + S _).
  rewrite -> plus_n_Sm.
  rewrite -> Nat.add_1_r.
  reflexivity.
Qed.


(* ********** *)

Definition specification_of_the_mystery_function_d (mf : nat -> nat -> bool) :=
  (forall j : nat,
      mf 0 j = true)
  /\
  (forall i : nat,
      mf (S i) 0 = false)
  /\
  (forall i j : nat,
      mf (S i) (S j) = mf i j).


Definition unit_test_for_the_mystery_function_d (mf : nat -> nat -> bool) :=
(*
   The following equality is in the specification:
*)
  (mf 0 0 =b= true)
  &&
  (mf 0 1 =b= true)
  &&
  (mf 1 0 =b= false)
  &&
  (* mf 1 1 = mf 0 0 = true *)
  (mf 1 1 =b= true)
  &&
  (* mf 1 2 = mf 0 1 = true *)
  (mf 1 2 =b= true)
  &&
  (* mf 2 1 = mf 1 0 = false *)
  (mf 2 1 =b= false)
  &&
  (* mf 2 2 = mf 0 1 = true *)
  (mf 2 2 =b= true)
  &&
  (* mf 2 10 = mf 0 8 = true *)
  (mf 2 10 =b= true)
  .

Proposition there_is_at_most_one_mystery_function_d :
  forall f g : nat -> nat -> bool,
    specification_of_the_mystery_function_d f ->
    specification_of_the_mystery_function_d g ->
    forall k l : nat,
      f k l = g k l.
Proof.
  intros f g. 
  unfold specification_of_the_mystery_function_d.
  intros [S_f_0_l [S_f_0_r S_f_S]] [S_g_0_l [S_g_0_r S_g_S]].
  intro k.
  induction k as [ | k' IHk'].
  intro l.
  rewrite -> S_f_0_l.
  rewrite -> S_g_0_l.
  reflexivity.

  intro l.
  induction l as [ | l' IHl'].
  rewrite -> S_f_0_r.
  rewrite -> S_g_0_r.
  reflexivity.

  rewrite -> S_f_S.
  rewrite -> S_g_S.
  rewrite -> IHk'.
  reflexivity.
Qed.

Fixpoint less_than_or_eq (i j : nat) : bool :=
  match i with
  | O =>
    true
  | S i' =>
    match j with
    | O =>
      false
    | S j' =>
      less_than_or_eq i' j'
    end
  end.

Lemma unfold_less_than_or_eq_0_l :
  forall j : nat,
    less_than_or_eq 0 j = true.
Proof.
  unfold_tactic less_than_or_eq.
Qed.

Lemma unfold_less_than_or_eq_0_r :
  forall i' : nat,
    less_than_or_eq (S i') 0 = false.
Proof.
  unfold_tactic less_than_or_eq.
Qed.

Lemma unfold_less_than_or_eq_SS :
  forall i' j' : nat,
    less_than_or_eq (S i') (S j') = less_than_or_eq i' j'. 
Proof.
  unfold_tactic less_than_or_eq.
Qed.

Compute (unit_test_for_the_mystery_function_d less_than_or_eq).

Theorem there_is_at_least_one_mystery_function_d :
  specification_of_the_mystery_function_d less_than_or_eq.
Proof.
  unfold specification_of_the_mystery_function_d.
  split.
    exact unfold_less_than_or_eq_0_l.
  split.
    exact unfold_less_than_or_eq_0_r.
  exact unfold_less_than_or_eq_SS.
Qed.
(* ********** *)

Definition specification_of_the_mystery_function_e (mf : nat -> bool) :=
  (mf 0 = false)
  /\
  (mf 1 = true)
  /\
  (forall i j : nat,
      mf (i + j) = xorb (mf i) (mf j)).

Definition unit_test_for_the_mystery_function_e (mf : nat -> bool) :=
(*
   The following equality is in the specification:
*)
  (mf 0 =b= false)
  &&
  (mf 1 =b= true)
  &&
  (*mf 1 + 1 = xorb (mf 1) (mf 1) = false*) 
  (mf 2 =b= false)
  &&
  (*mf 1 + 2 = xorb (mf 1) (mf 2) = true*) 
  (mf 3 =b= true)
  &&
  (*mf 2 + 2 = xorb (mf 2) (mf 2) = false*) 
  (mf 4 =b= false)
  &&
  (*mf 2 + 3 = xorb (mf 2) (mf 3) = true*) 
  (mf 5 =b= true)
  &&
  (mf 123 =b= true)
  &&
  (mf 124 =b= false).


Proposition there_is_at_most_one_mystery_function_e :
  forall f g : nat -> bool,
    specification_of_the_mystery_function_e f ->
    specification_of_the_mystery_function_e g ->
    forall k : nat,
      f k = g k.
Proof.
  intros f g. 
  unfold specification_of_the_mystery_function_d.
  intros [S_f_0 [S_f_1 S_f_S]] [S_g_0 [S_g_1 S_g_S]].
  intro k.
  induction k as [ | k' IHk'].
  rewrite -> S_f_0.
  rewrite -> S_g_0.
  reflexivity.

  rewrite <- Nat.add_1_r.
  rewrite -> S_f_S.
  rewrite -> S_g_S.
  rewrite -> S_f_1.
  rewrite -> S_g_1.
  rewrite -> IHk'.
  reflexivity.
Qed.

(* With an inherited attribute, lambda-lifted: 

Fixpoint visit_odd_v2 (n : nat) (a : bool) : bool :=
  match n with
  | 0 => a
  | S n' => visit_odd_v2 n' (negb a)
  end.

Definition odd_v2 (n : nat) : bool :=
  visit_odd_v2 n false.

Compute (unit_test_for_the_mystery_function_e odd_v2).
*)


Fixpoint odd_v1 (n : nat) : bool :=
  match n with
  | 0 => false
  | S n' => match n' with
            | 0 => true
            | S n'' => odd_v1 n''
            end
  end.

Compute (unit_test_for_the_mystery_function_e odd_v1).

Lemma unfold_odd_v1_0 :
  odd_v1 0 = false.
Proof.
  unfold_tactic odd_v1.
Qed.

Lemma unfold_odd_v1_1:
  odd_v1 (S 0) = true.
Proof.
  unfold_tactic odd_v1.
Qed.

Lemma unfold_odd_v1_SSn'' :
  forall n'' : nat,
  odd_v1 (S (S n'')) = odd_v1 n''.
Proof.
  unfold_tactic odd_v1.
Qed.

Lemma about_odd_v1:
  forall n' : nat,
    odd_v1 (S n') = negb (odd_v1 n').
Proof.
  intro n''.
  induction n'' as [ | n'' IHn''].

  rewrite -> (unfold_odd_v1_1).
  rewrite -> (unfold_odd_v1_0).
  unfold negb.
  reflexivity.

  rewrite -> (unfold_odd_v1_SSn'').
  rewrite -> IHn''. 
  rewrite -> negb_involutive.
  reflexivity.
Qed.

Theorem there_is_at_least_one_mystery_function_e :
  specification_of_the_mystery_function_e odd_v1.
Proof.
  unfold specification_of_the_mystery_function_e.
  split.
    exact unfold_odd_v1_0.
  split.
    exact unfold_odd_v1_1.
  intro i.
  induction i as [ | i' IHi'].
  intro j.
  rewrite -> Nat.add_0_l.
  induction j as [ | j' IHj'].
  rewrite -> unfold_odd_v1_0.
  unfold xorb.
  reflexivity.

  rewrite -> about_odd_v1.
  Search (negb _ = xorb _ (negb _)).
  rewrite <- negb_xorb_r.
  rewrite <- IHj'.
  reflexivity.  

  intro j.
  rewrite -> plus_Sn_m.
  rewrite ->2 about_odd_v1.
  (*negb_xorb_r: forall b b' : bool, negb (xorb b b') = xorb b (negb b')*)
  rewrite <- negb_xorb_l.
  rewrite <- IHi'.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_f (mf : nat -> bool) :=
  (mf 0 = false)
  /\
  (mf 1 = true)
  /\
  (forall i j : nat,
      mf (i + j) = (mf i =b= mf j)).

 
Definition unit_test_for_the_mystery_function_f (mf : nat ->bool) :=
  (mf 0 =b= false)
  &&
  (mf 1 =b= true)
  &&
  (*mf (1 + 1) = (mf 1 =b= mf 1))*)
  (mf 2 =b= true)
  &&
  (*mf (2 + 0) = (mf 2 =b= mf 0))*)
  (mf 2 =b= false)
  &&
  (*mf (1 + 2) = (mf 1 =b= mf 2))*)
  (mf 3 =b= true)
  &&
  (*mf (3 + 0) = (mf 3 =b= mf 0))*)
  (mf 3 =b= false).

Lemma a_contradictory_aspect_of_the_mystery_function_f :
  forall mf : nat -> bool,
    specification_of_the_mystery_function_f mf ->
    mf 2 = true /\ mf 2 = false.
Proof.
  unfold specification_of_the_mystery_function_f.
  intros mf [S_mf_0 [S_mf_1 S_mf_SS]]. 
  split.

  Search (2 = 1 + 1).
  rewrite -> BinInt.ZL0.
  rewrite -> S_mf_SS.
  rewrite -> S_mf_1.
  unfold eqb.
  reflexivity.

  Check (Nat.add_0_r).
  rewrite <- (Nat.add_0_r 2).
  rewrite -> BinInt.ZL0.
  rewrite ->2 S_mf_SS.
  rewrite -> S_mf_1.
  rewrite -> S_mf_0.
  unfold eqb.
  reflexivity.
Qed.

Theorem there_are_zero_mystery_functions_f :
  forall mf : nat -> bool,
    specification_of_the_mystery_function_f mf ->
    exists n : nat,
      mf n <> mf n.
Proof.
   intros mf S_mf.
   assert (H_contr := a_contradictory_aspect_of_the_mystery_function_f).
   assert (H_contr_eg := S_mf).
   apply H_contr in H_contr_eg.
   destruct H_contr_eg as [mf_2_true mf_2_false].
   exists 2.
   rewrite -> mf_2_true at 1.
   rewrite -> mf_2_false at 1.
   Search (true <> false).
   exact diff_true_false.
Qed.  
  (* ********** *)

Definition specification_of_the_mystery_function_g (mf : nat -> nat) :=
  (mf 1 = 1)
  /\
  (forall i j : nat,
      mf (i + j) = mf i + 2 * i * j + mf j).
 
Definition unit_test_for_the_mystery_function_g (mf : nat -> nat) :=
  (mf 1 =n= 1).
(*mf 0 =n= mf 0 + 2 * 0 * 0 + mf 0*)
(*mf 0 = ??*)
(* ********** *)

Definition specification_of_the_mystery_function_h (mf : nat -> nat) :=
  (mf 1 = 1)
  /\
  (forall i : nat,
      mf (S (S i)) = (S (S i)) * mf (S i)).

(* ********** *)

Definition specification_of_the_mystery_function_i (mf : nat -> nat) :=
  (forall q : nat,
      mf (2 * q) = q)
  /\
  (forall q : nat,
      mf (S (2 * q)) = q).

Definition unit_test_for_the_mystery_function_i (mf : nat -> nat) :=
  (mf 0 =n= 0)&&
  (mf 1 =n= 0)&&
  (mf 2 =n= 1)&&
  (mf 3 =n= 1)&&
  (mf 4 =n= 2)&&
  (mf 5 =n= 2)&&
  (mf 6 =n= 3)&&
  (mf 7 =n= 3)&&
  (mf 100 =n= 50)&&
  (mf 101 =n= 50).

Lemma about_i : 
    forall f : nat -> nat,
    specification_of_the_mystery_function_i f ->
    forall q : nat,
      f (S (2 * q)) = f (2 * q). 
Proof.
  intro f.
  unfold specification_of_the_mystery_function_i.
  intros [S_f_2q S_f_S] q.
  rewrite -> S_f_2q.
  rewrite -> S_f_S.
  reflexivity.
Qed.


Lemma about_i' : 
    forall f : nat -> nat,
    specification_of_the_mystery_function_i f ->
    forall q : nat,
      f (S (S (2 * q))) = S (f (2 * q)). 
Proof.
  intro f.
  unfold specification_of_the_mystery_function_i.
  intros [S_f_2q S_f_S] q.
  rewrite -> S_f_2q.
  Search (1 + _ = _).
  rewrite <- Nat.add_1_l.
  rewrite <- (Nat.add_1_l (2 * q)).
Admitted.

Proposition there_is_at_most_one_mystery_function_i : 
  forall f g : nat -> nat,
    specification_of_the_mystery_function_i f ->
    specification_of_the_mystery_function_i g ->
    forall k : nat,
      f k = g k.
Proof.
  intros f g. 
  unfold specification_of_the_mystery_function_i.
  intros [S_f_2q S_f_S] [S_g_2q S_g_S].
  intro k.
  induction k as [ | k' IHk'].
  Search (_ * 0 = 0).
  rewrite <- (Nat.mul_0_r 2).
  rewrite -> S_f_2q.
  rewrite -> S_g_2q.
  reflexivity.
 
  induction k' as [ | k'' IHk''].
  rewrite <- (Nat.add_0_r 1).
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite <- (Nat.mul_0_r 2) at 1.
  rewrite <- (Nat.mul_0_r 2) at 4.
  rewrite -> (Nat.add_0_r (2 * 0)).
  rewrite -> S_f_S.
  rewrite -> S_g_S.
  reflexivity.
Abort.
   
  
Fixpoint mf_i (n : nat) : nat :=
  match n with
  | O =>
    0
  | S n' =>
    match n' with
    | O => 0
    | S n'' => S (mf_i n'')
    end
  end.

Compute (unit_test_for_the_mystery_function_i mf_i).

Lemma mf_i_0 :
  mf_i 0 = 0.
Proof.
  unfold_tactic mf_i.
Qed.

Lemma mf_i_S :
  forall n' : nat,
  mf_i (S n') = match n' with
                | O => 0
                | S n'' => 1 + mf_i n''
                end.
Proof.
  unfold_tactic mf_i.
Qed.

Lemma mf_i_1 :
  mf_i 1 = 0.
Proof.
  unfold_tactic mf_i.
Qed.

Lemma mf_i_SS :
  forall n'' : nat,
  mf_i (S (S n'')) = S (mf_i n'').
Proof.
  unfold_tactic mf_i.
Qed.


Theorem there_is_at_least_one_mystery_function_i :
  specification_of_the_mystery_function_i mf_i.
Proof.
  unfold specification_of_the_mystery_function_i.
  split.
  induction q as [ | q' IHq'].
  rewrite -> Nat.mul_0_r.
  exact mf_i_0.
  
  rewrite <- (Nat.add_1_l q') at 1.
  rewrite -> (Nat.mul_add_distr_l 2 1 q').
  rewrite -> (Nat.mul_1_r).
  Search (_ + _ = _ + _).
  rewrite -> Nat.add_comm.
  rewrite -> BinInt.ZL0 at 2.
  rewrite -> (Nat.add_assoc (2 * q') 1 1).
  rewrite ->2 (Nat.add_1_r).
  rewrite -> mf_i_SS.
  rewrite -> IHq'.
  reflexivity.

  induction q as [ | q' IHq'].
  rewrite -> Nat.mul_0_r.
  rewrite -> mf_i_1.
  reflexivity.

  rewrite <- (Nat.add_1_l q') at 1.
  rewrite -> (Nat.mul_add_distr_l 2 1 q').
  rewrite -> (Nat.mul_1_r).
  Search (_ + _ = _ + _).
  rewrite -> Nat.add_comm.
  rewrite -> BinInt.ZL0 at 2.
  rewrite -> (Nat.add_assoc (2 * q') 1 1).
  rewrite ->2 (Nat.add_1_r).
  rewrite -> mf_i_SS.
  rewrite -> IHq'.
  reflexivity.
Qed.
(* ********** *)
Definition specification_of_the_mystery_function_j (mf : nat -> bool) :=
  (forall q : nat,
      mf (3 * q) = true)
  /\
  (forall q : nat,
      mf (S (3 * q)) = false)
  /\
  (forall q : nat,
      mf (S (S (3 * q))) = false).

(* ********** *)

Definition specification_of_the_mystery_function_k (mf : nat -> nat) :=
  (mf 0 = 0)
  /\
  (mf 1 = 1)
  /\
  (mf 2 = 1)
  /\
  (forall p q : nat,
    mf (S (p + q)) = mf (S p) * mf (S q) + mf p * mf q).

(*
Proposition induction_two (P : nat -> Prop):
  P 0 ->
  P 1 ->
  (forall n, P n -> P (S n) -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros H0 H1 Hn n.
  assert (P n /\ P (S n)).
  induction n as [ | n' IHn'].
  split.
  apply H0.
  apply H1.
  split.
  apply IHn'.
  apply Hn.
  apply IHn'.
  apply IHn'.
  apply H.
 Qed.*)

Proposition there_is_at_most_one_mystery_function_k :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_k f ->
    specification_of_the_mystery_function_k g ->
    forall n : nat,
      f n = g n.
Proof.
   intros f g.
  unfold specification_of_the_mystery_function_k.
  intros [S_f_0 [S_f_1 [S_f_2 S_f_S]]] [S_g_0 [S_g_1 [S_g_2 S_g_S]]].
  assert (H_both : forall n : nat, f n = g n /\ f (S n) = g (S n)).
  induction n as [ | n'' [IHn'' IHSn'']].
  split.
    rewrite -> S_f_0.
    rewrite -> S_g_0.
    reflexivity.
  rewrite -> S_f_1.
  rewrite -> S_g_1.  
  reflexivity.
  split.
  exact IHSn''.
  rewrite <- Nat.add_1_r.
  rewrite -> plus_Sn_m.
  rewrite -> S_f_S.
  rewrite -> S_g_S.
  rewrite -> S_f_1.
  rewrite -> S_f_2.
  rewrite -> S_g_1.
  rewrite -> S_g_2.
  rewrite -> IHn''.
  rewrite -> IHSn''. 
  reflexivity.
  intro n.
  destruct (H_both n) as [H_n _].
  exact H_n.
  (*
    By induction principle: 
  Restart.
  intros f g.
  unfold specification_of_the_mystery_function_k.
  intros [S_f_0 [S_f_1 [S_f_2 S_f_S]]] [S_g_0 [S_g_1 [S_g_2 S_g_S]]].
  intro n.
  induction n as [ | | n'' IHn'' IHSn''] using induction_two.
  
  rewrite -> S_f_0.
  rewrite -> S_g_0.
  reflexivity.

  rewrite -> S_f_1.
  rewrite -> S_g_1.
  reflexivity.
  rewrite <- Nat.add_1_r.
  rewrite -> plus_Sn_m.
  rewrite -> S_f_S.
  rewrite -> S_g_S.
  rewrite -> S_f_1.
  rewrite -> S_f_2.
  rewrite -> S_g_1.
  rewrite -> S_g_2.
  rewrite -> IHn''.
  rewrite -> IHSn''. 
  reflexivity.
*)
Qed.

Definition unit_test_for_the_mystery_function_k (mf : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (mf 0 =n= 0)
  &&
  (mf 1 =n= 1)
  &&
  (mf 2 =n= 1)
  &&
  (* mf 3 = mf (S (1+1)) = mf (S 1) * mf (S 1) + mf 1 * mf 1 = 2 *)
  (mf 3 =n= 2)
  &&
  (* mf 4 = mf (S (1+2)) = mf (S 1) * mf (S 2) + mf 1 * mf 2 = 
                         = 1 * 2 + 1 * 1 
                         = 3 *)
  (mf 4 =n= 3)
  &&
  (mf 5 =n= 5)
  &&
  (mf 6 =n= 8).

Fixpoint fib (n: nat) : nat:=
  match n with
  | 0 => O
  | S n' => match n' with
            | O => 1
            | S n'' => fib n' + fib n''
            end
  end.

Compute unit_test_for_the_mystery_function_k fib.

Lemma unfold_fib_0:
  fib 0 = 0.
Proof.
  unfold_tactic fib.
Qed.

Lemma unfold_fib_1:
  fib 1 = 1.
Proof.
  unfold_tactic fib.
Qed.

Lemma unfold_fib_SSn:
  forall (n'': nat),
  fib (S (S n'')) = fib (S n'') + fib n''.
Proof.
  unfold_tactic fib.
Qed.
  
Theorem there_is_at_least_one_mystery_function_k :
  specification_of_the_mystery_function_k fib.
Proof.
  unfold specification_of_the_mystery_function_k.
  split. 
  rewrite -> unfold_fib_0.
  reflexivity.

  split.
  rewrite -> unfold_fib_1.
  reflexivity.

  split.
  rewrite -> unfold_fib_SSn.
  rewrite -> unfold_fib_1.
  rewrite -> unfold_fib_0.
  rewrite -> (Nat.add_0_r 1).
  reflexivity.

  intro p.
  induction p as [ | p' IHp'].
  intro q.
  rewrite -> unfold_fib_1.
  rewrite -> unfold_fib_0.
  Search (0 * _ = 0).
  rewrite -> (Nat.mul_0_l (fib q)).
  rewrite -> (Nat.add_0_r (1 * fib (S q))).
  rewrite -> (Nat.mul_1_l (fib (S q))).
  rewrite -> (Nat.add_0_l q).
  reflexivity.

  intro q.
  Search (S _ + _ = _ + S _).
  rewrite -> (plus_Snm_nSm p' q).
  rewrite -> (IHp' (S q)).
  rewrite -> (unfold_fib_SSn p').
  rewrite -> (unfold_fib_SSn q).
  Search (_ * (_ + _) = _ * _ + _ * _).
  rewrite -> (Nat.mul_add_distr_l (fib (S p')) (fib (S q)) (fib q)).
  Search (_ * _ = _ * _).
  rewrite -> (Nat.mul_comm (fib (S p') + fib p') (fib (S q))).
  rewrite -> (Nat.mul_add_distr_l (fib (S q)) (fib (S p')) (fib p')).
  Search (_ + _ = _ + _).
  rewrite -> (Nat.add_shuffle0 (fib (S p') * fib (S q)) (fib (S p') * fib q) (fib p' * fib (S q))).
  rewrite -> (Nat.mul_comm (fib p') (fib (S q))).
  rewrite -> (Nat.mul_comm (fib (S p')) (fib (S q))).
  reflexivity.
Qed.  
  (* ********** *)

Definition specification_of_the_mystery_function_l (mf : nat -> nat) :=
  (mf 0 = 0)
  /\
  (mf 1 = 1)
  /\
  (mf 2 = 1)
  /\
  (forall n''' : nat,
    mf n''' + mf (S (S (S n'''))) = 2 * mf (S (S n'''))).

Definition unit_test_for_the_mystery_function_l (mf : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (mf 0 =n= 0)
  &&
  (mf 1 =n= 1)
  &&
  (mf 2 =n= 1)
  &&
  (* mf 3 = 2 * mf 2 - mf 0 
          = 2
*)
  (mf 3 =n= 2)
  &&
  (* mf 4 = 2 * mf 3 - mf 1 
          = 3
*)
  (mf 4 =n= 3)
  &&
  (mf 5 =n= 5)
  &&
  (mf 6 =n= 8).
  (*
Assuming mf (n+2) = mf (n+1) + mf (n): 

    mf (n) + mf (n+3) = 2 * mf (n+2)
 -> mf (n+3) = 2 * mf (n+2) - mf (n)
             = mf (n+1) + mf (n) + mf (n+2) - mf n
             =  mf (n+2) + mf (n+1)
*)

(*
Proposition induction_three (P : nat -> Prop):
  P 0 ->
  P 1 -> 
  P 2 ->
  (forall n, P n -> P (S (S n)) -> P (S (S (S n)))) ->
  forall n, P n.
Proof.
  intros H0 H1 H2 Hn n.
  assert (P n /\ P (S n) /\ P (S (S n))).
  induction n as [ | n' IHn'].
  split.
  apply H0.
  split.
  apply H1.
  apply H2.
  split.
  apply IHn'.
  split.
  apply IHn'.
  apply Hn.

  apply IHn'.
  apply IHn'.
  apply H.
 Qed.
*)
 
Proposition there_is_at_most_one_mystery_function_l :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_l f ->
    specification_of_the_mystery_function_l g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g. 
  unfold specification_of_the_mystery_function_l.
  intros [S_f_0 [S_f_1 [S_f_2 S_f_S]]] [S_g_0 [S_g_1 [S_g_2 S_g_S]]].
  intro n'''.
  assert (H_three : forall n : nat, f n = g n
                                    /\
                                    f (S n) = g (S n)
                                    /\
                                    f (S (S n)) = g (S (S n))).
  induction n as [ | n'' [IHn'' [IHSn'' IHSSn'']]]. 
  split.
    rewrite -> S_f_0.
    rewrite -> S_g_0.
    reflexivity.
  split.
    rewrite -> S_f_1.
    rewrite -> S_g_1.
    reflexivity.
  rewrite -> S_f_2.
  rewrite -> S_g_2.
  reflexivity.
  split.
    exact IHSn''.
  split.
    exact IHSSn''.
  Check Nat.add_sub_eq_l.
  apply (Nat.add_sub_eq_l (2 * f (S (S n'')))) in S_f_S.
  apply (Nat.add_sub_eq_l (2 * g (S (S n'')))) in S_g_S.
  rewrite <- S_f_S.
  rewrite <- S_g_S.
  rewrite -> IHSSn''.
  rewrite -> IHn''.
  reflexivity.
  destruct (H_three n''') as [H_n''' _ _].
  exact H_n'''.

 
  (*
    By induction principle: 

  Restart.        
  intros f g. 
  unfold specification_of_the_mystery_function_l.
  intros [S_f_0 [S_f_1 [S_f_2 S_f_S]]] [S_g_0 [S_g_1 [S_g_2 S_g_S]]].
  intro n.
  induction n as [ | | | n IHn IHSn] using induction_three.
  rewrite -> S_f_0.
  rewrite -> S_g_0.
  reflexivity.
  
  rewrite -> S_f_1.
  rewrite -> S_g_1.
  reflexivity.
  
  rewrite -> S_f_2.
  rewrite -> S_g_2.
  reflexivity.
  apply (Nat.add_sub_eq_l (2 * f (S (S n)))) in S_f_S.
  apply (Nat.add_sub_eq_l (2 * g (S (S n)))) in S_g_S.
  rewrite <- S_f_S.
  rewrite <- S_g_S.
  rewrite -> IHSn.
  rewrite -> IHn.
  reflexivity.
*)
  Qed.
  
Theorem there_is_at_least_one_mystery_function_l :
  specification_of_the_mystery_function_l fib.
Proof.
  unfold specification_of_the_mystery_function_l.
  split.
    exact unfold_fib_0.
  split.
    exact unfold_fib_1.
  split.
    unfold fib.
    reflexivity.
  intro n.
  rewrite -> (unfold_fib_SSn (S n)).
  Search (_ + (_ + _) = _ + (_ + _)).
  rewrite -> Nat.add_shuffle3.
  rewrite -> (Nat.add_comm (fib n)).
  rewrite <- (unfold_fib_SSn n).
  Search (_ * _ = _).
  (*Nat.mul_succ_l: forall n m : nat, S n * m = n * m + m*)
  rewrite -> (Nat.mul_succ_l 1 (fib (S (S n)))).
  rewrite -> Nat.mul_1_l.
  reflexivity.
Qed.
  (* ********** *)

(* Binary trees of natural numbers: *)

Inductive tree : Type :=
  | Leaf : nat -> tree
  | Node : tree -> tree -> tree.


Fixpoint beq_t_t A B :=
  match A with
  | Leaf n1 => match B with
               |Leaf n2 => (n1 =n= n2)
               |Node _ _ => false
               end
  | Node t1 t2 => match B with
                  |Leaf n1 => false
                  |Node t3 t4 => (beq_t_t t1 t3) && (beq_t_t t2 t4)
                  end
  end.

Notation "A =t= B" :=
  (beq_t_t A B) (at level 70, right associativity).

Definition specification_of_the_mystery_function_m (mf : tree -> tree) :=
  (forall n : nat,
      mf (Leaf n) = Leaf n)
  /\
  (forall (n : nat)
          (t : tree),
      mf (Node (Leaf n) t) = Node (Leaf n) (mf t))
  /\
  (forall t11 t12 t2 : tree,
      mf (Node (Node t11 t12) t2) = mf (Node t11 (Node t12 t2))).


Definition unit_test_for_the_mystery_function_m (mf : tree -> tree) :=
(*
   The following equality is in the specification:
*)
  (mf (Leaf 1) =t= Leaf 1)
  &&
  (mf (Node (Leaf 1) (Leaf 2)) =t= Node (Leaf 1) (Leaf 2))
.


(* You might not manage to prove
   that at most one function satisfies this specification (why?),
   but consider whether the following function does.
   Assuming it does, what does this function do?
 *)

Fixpoint mystery_function_m_aux (t a : tree) : tree :=
  match t with
  | Leaf n =>
    Node (Leaf n) a
  | Node t1 t2 =>
    mystery_function_m_aux t1 (mystery_function_m_aux t2 a)
  end.

Fixpoint mystery_function_m (t : tree) : tree :=
  match t with
  | Leaf n =>
    Leaf n
  | Node t1 t2 =>
    mystery_function_m_aux t1 (mystery_function_m t2)
  end.

(**************)

Lemma unfold_m_Leaf:
  forall n : nat,
    mystery_function_m (Leaf n) = Leaf n.
Proof.
  unfold_tactic mystery_function_m.
Qed.

Lemma unfold_m_Node :
  forall t1 t2 : tree,
    mystery_function_m (Node t1 t2) = 
    mystery_function_m_aux t1 (mystery_function_m t2).
Proof.
  unfold_tactic mystery_function_m.
Qed.

(************)
Lemma unfold_m_aux_Leaf:
  forall (n : nat) (a: tree),
    mystery_function_m_aux (Leaf n) a = Node (Leaf n) a.
Proof.
  unfold_tactic mystery_function_m_aux.
Qed.

Lemma unfold_m_aux_Node :
  forall t1 t2 a : tree,
    mystery_function_m_aux (Node t1 t2) a = 
    mystery_function_m_aux t1 (mystery_function_m_aux t2 a).
Proof.
  unfold_tactic mystery_function_m_aux.
Qed.

(************)
      
Theorem there_is_at_least_one_mystery_function_m :
  specification_of_the_mystery_function_m mystery_function_m.
Proof.
  unfold specification_of_the_mystery_function_m.
  split.
  intro n.
  rewrite -> (unfold_m_Leaf n).
  reflexivity.

  split.
  intros n t2.
  rewrite -> (unfold_m_Node (Leaf n) t2).
  rewrite -> (unfold_m_aux_Leaf n (mystery_function_m t2)).
  reflexivity.

  intros t1 t2 t3.
  rewrite -> (unfold_m_Node (Node t1 t2) t3).
  rewrite -> (unfold_m_aux_Node t1 t2 (mystery_function_m t3)).
  rewrite -> (unfold_m_Node t1 (Node t2 t3)).
  rewrite -> (unfold_m_Node t2 t3).
  reflexivity.
Qed.
(* ********** *)
(* end of week-07_mystery-functions.v *)