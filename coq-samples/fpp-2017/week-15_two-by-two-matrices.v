(* week-15_two-by-two-matrices.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Tue 21 Nov 2017 *)

(* ********** *)

(*
   name:Jeremy Yew
   student ID number:A0156262H
   e-mail address:jeremy.yew@u.yale-nus.edu.sg
*)

(* ********** *)

Ltac unfold_tactic name :=
  intros;
  unfold name; (* fold name; *)
  reflexivity.
  
Require Import Arith Bool.

(* ********** *)

(* The goal of this project is to study 2x2 matrices,
   along the lines of Section 5 of
     http://users-cs.au.dk/danvy/more-about-induction-proofs.pdf
*)

Inductive m22 : Type :=
| M22 : nat -> nat -> nat -> nat -> m22.


(*
1. Definition 9: Multiplication of 2*2 matrices
 *)

(*
|x11 x12|   |y11 y12|
|x21 x22| * |y21 y22|
 *)

Definition mul_m22 (X Y : m22) : m22 :=
  match X with
  | M22 x11 x12
        x21 x22 =>
    match Y with
    | M22 y11 y12
          y21 y22 =>
      M22 (x11 * y11 + x12 * y21) (x11 * y12 + x12 * y22)
          (x21 * y11 + x22 * y21) (x21 * y12 + x22 * y22)
    end
  end.

Compute mul_m22 (M22 1 2 3 4) (M22 1 0 0 1).

Lemma unfold_mul_m22:
  forall (x11 x12 x21 x22 y11 y12 y21 y22 : nat),
    mul_m22 (M22 x11 x12 x21 x22) (M22 y11 y12 y21 y22)
            = M22 (x11 * y11 + x12 * y21) (x11 * y12 + x12 * y22)
                  (x21 * y11 + x22 * y21) (x21 * y12 + x22 * y22).
Proof.
  unfold_tactic mul_m22.
Qed.

  (*
2. Addition of Matrices
*)

Definition add_m22 (X Y : m22) : m22 :=
  match X with
  | M22 x11 x12
        x21 x22 =>
    match Y with
    | M22 y11 y12
          y21 y22 =>
      M22 (x11 + y11) (x12 + y12)
          (x21 + y21) (x22 + y22)
    end
  end.

(*
3. Definitions 11 and 13
*)

Definition I :=
  M22 1 0 0 1.
  
Fixpoint exp_m22 (n : nat) (M : m22) : m22 :=
  match n with
  | O =>
    I
  | S n' => mul_m22 (exp_m22 n' M) M
  end.

Lemma unfold_exp_m22_O:
  forall (M : m22),
    exp_m22 0 M = I.
Proof.  
  unfold_tactic exp_m22.
Qed.
Lemma unfold_exp_m22_S:
  forall (n' : nat) (M : m22),
    exp_m22 (S n') M = mul_m22 (exp_m22 n' M) M.
Proof.  
  unfold_tactic exp_m22.
Qed.

(*
4. Properties 10 and 12
 *)

Lemma shuffle_helper:
  forall (n m p q : nat),
    n + m + p + q = n + p + m + q.
Proof.
  intros n m p q.
  Check (Nat.add_assoc).
  rewrite <- Nat.add_assoc.
  rewrite -> Nat.add_shuffle1.
  rewrite -> Nat.add_assoc.
  reflexivity.
Qed.

Theorem mul_m22_associative:
  forall (X Y Z : m22),
    mul_m22 X (mul_m22 Y Z) = mul_m22 (mul_m22 X Y) Z. 
Proof.
  intros X Y Z.
  induction X as [x11 x12 x21 x22].
  induction Y as [y11 y12 y21 y22].
  induction Z as [z11 z12 z21 z22].
  rewrite ->4 unfold_mul_m22.
  Check (Nat.mul_add_distr_l).
  rewrite ->8 Nat.mul_add_distr_l.
  rewrite ->8 Nat.mul_add_distr_r.
  Check (Nat.mul_assoc).
  rewrite -> 16 Nat.mul_assoc.
  rewrite ->8 Nat.add_assoc.
  rewrite -> (shuffle_helper _ (x11 * y12 * z21) (x12 * y21 * z11) _).
  rewrite -> (shuffle_helper _ (x11 * y12 * z22) (x12 * y21 * z12) _).
  rewrite -> (shuffle_helper _ (x21 * y12 * z21) (x22 * y21 * z11) _).
  rewrite -> (shuffle_helper _ (x21 * y12 * z22) (x22 * y21 * z12) _).
  reflexivity.
Qed.

Theorem I_neutral_mul_m22_l:
  forall (M : m22),
    mul_m22 I M = M.   
Proof.
  intro M.
  induction M as [x11 x12 x21 x22]. 
  unfold I.
  unfold mul_m22. 
  rewrite ->4 Nat.mul_1_l.
  rewrite ->4 Nat.mul_0_l.
  rewrite ->2 Nat.add_0_l.
  rewrite ->2 Nat.add_0_r.
  reflexivity.
Qed.


Theorem I_neutral_mul_m22_r:
  forall (M : m22),
    mul_m22 M I = M.   
Proof.
  intro M.
  induction M as [x11 x12 x21 x22]. 
  unfold I.
  unfold mul_m22. 
  rewrite ->4 Nat.mul_1_r.
  rewrite ->4 Nat.mul_0_r.
  rewrite ->2 Nat.add_0_l.
  rewrite ->2 Nat.add_0_r.
  reflexivity.
Qed.

(*
5. 
Proposition 14
*)

Proposition exponentiation_M22_1101:
  forall (n : nat),
    exp_m22 n (M22 1 1 0 1) = (M22 1 n 0 1).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  rewrite -> unfold_exp_m22_O.
  unfold I.
  reflexivity.

  rewrite -> unfold_exp_m22_S.
  rewrite -> IHn'.
  unfold mul_m22.
  rewrite -> Nat.mul_0_l.
  rewrite ->2 Nat.mul_0_r.
  rewrite ->2 Nat.mul_1_r.
  rewrite ->2 Nat.add_0_r.
  rewrite -> Nat.add_0_l.
  rewrite -> Nat.add_1_l at 1.
  reflexivity.
Qed.
(*
6. Exercise 28
*)

Fixpoint exp_m22_alt (n : nat) (M : m22) : m22 :=
  match n with
  | O =>
    I
  | S n' => mul_m22 M (exp_m22_alt n' M)
  end.

Lemma unfold_exp_m22_alt_O:
  forall (M : m22),
    exp_m22_alt 0 M = I.
Proof.  
  unfold_tactic exp_m22_alt.
Qed.
Lemma unfold_exp_m22_alt_S:
  forall (n' : nat) (M : m22),
    exp_m22_alt (S n') M = mul_m22 M (exp_m22_alt n' M).
Proof.  
  unfold_tactic exp_m22_alt.
Qed.

Proposition exponentiation_M22_1101':
  forall (n : nat),
    exp_m22_alt n (M22 1 1 0 1) = (M22 1 n 0 1).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  rewrite -> unfold_exp_m22_alt_O.
  unfold I.
  reflexivity.

  rewrite -> unfold_exp_m22_alt_S.
  rewrite -> IHn'.
  unfold mul_m22.
  rewrite ->2 Nat.mul_0_l.
  rewrite -> Nat.mul_0_r.
  rewrite -> Nat.mul_1_r.
  rewrite -> Nat.mul_1_l.
  rewrite ->2 Nat.add_0_r.  
  rewrite -> Nat.add_0_l.
  rewrite -> Nat.add_1_r.
  reflexivity.
Qed.

(*
7. Proposition 29
*)

Proposition about_exp_m22_S:
  forall (n : nat) (M : m22),
    mul_m22 M (exp_m22 n M) = mul_m22 (exp_m22 n M) M. 
Proof.
  intros n M.
  induction n as [ | n' IHn'].

  rewrite -> unfold_exp_m22_O.
  rewrite -> I_neutral_mul_m22_l.
  rewrite -> I_neutral_mul_m22_r.
  reflexivity.

  rewrite -> unfold_exp_m22_S.
  rewrite -> mul_m22_associative.
  rewrite -> IHn'.
  reflexivity.
Qed.  

(*
8. Exercise 31
*)

Proposition about_exp_m22_S':
  forall (n : nat) (M : m22),
    mul_m22 M (exp_m22_alt n M) = mul_m22 (exp_m22_alt n M) M. 
Proof.
  intros n M.
  induction n as [ | n' IHn'].

  rewrite -> unfold_exp_m22_alt_O.
  rewrite -> I_neutral_mul_m22_l.
  rewrite -> I_neutral_mul_m22_r.
  reflexivity.

  rewrite -> unfold_exp_m22_alt_S.
  rewrite -> IHn'.
  rewrite -> mul_m22_associative.
  rewrite -> IHn'.
  reflexivity.
Qed.  

(* 
9. Corollary 32
*)

Corollary equivalence_of_exp_m22_and_exp_m22_alt:
  forall (n : nat) (M : m22),
    exp_m22 n M = exp_m22_alt n M.
Proof.
  intros n M.
  induction n as [ | n IHn'].

  rewrite -> unfold_exp_m22_O.
  rewrite -> unfold_exp_m22_alt_O.
  reflexivity.

  rewrite -> unfold_exp_m22_S.
  rewrite -> unfold_exp_m22_alt_S.
  rewrite <- IHn'.
  rewrite -> about_exp_m22_S.
  reflexivity.
Qed.

(*
10. Exercise 34 
 *)

Proposition exponentiation_M22_1011:
  forall (n : nat),
    exp_m22 n (M22 1 0 1 1) = M22 1 0 n 1.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  
  rewrite -> unfold_exp_m22_O.
  unfold I.
  reflexivity.

  rewrite -> unfold_exp_m22_S.
  rewrite -> IHn'.
  unfold mul_m22.
  rewrite -> Nat.mul_0_l.
  rewrite ->2 Nat.mul_0_r.
  rewrite ->2 Nat.add_0_r.
  rewrite -> Nat.add_0_l.
  rewrite ->2 Nat.mul_1_r.
  rewrite -> Nat.add_1_r at 1.
  reflexivity.
Qed.

(*
11. Definition 35
 *)

Definition transpose_m22 (M : m22) : m22 :=
 match M with
  | M22 x11 x12
        x21 x22 =>
    M22 x11 x21
        x12 x22
   end.

Compute transpose_m22 (M22 1 2 3 4).

(*
12. Proposition 36
*)

Proposition transposition_involutive:
  forall (M : m22),
    transpose_m22 (transpose_m22 M) = M.
Proof.
  intro M.
  induction M as [x11 x12 x21 x22].
  unfold transpose_m22.
  unfold transpose_m22.
  reflexivity.
Qed.

(*
13. Lemma 37
*)

Lemma transposition_distr_over_mul:
  forall (X Y : m22), 
  transpose_m22 (mul_m22 X Y) = mul_m22 (transpose_m22 Y) (transpose_m22 X).
Proof.
  intros X Y.
  induction X as [x11 x12 x21 x22].
  induction Y as [y11 y12 y21 y22].

  unfold mul_m22 at 1.
  unfold transpose_m22.
  unfold mul_m22.

  rewrite -> (Nat.mul_comm x11 y11).
  rewrite -> (Nat.mul_comm x12 y21).
  rewrite -> (Nat.mul_comm x21 y11).
  rewrite -> (Nat.mul_comm x22 y21).
  rewrite -> (Nat.mul_comm x11 y12).
  rewrite -> (Nat.mul_comm x12 y22).
  rewrite -> (Nat.mul_comm x21 y12).
  rewrite -> (Nat.mul_comm x22 y22).
  reflexivity.
Qed.

(*
14. Proposition 38
 *)
Proposition transp_and_exp_commutative:
  forall (n : nat) (M : m22),
    transpose_m22 (exp_m22 n M) = exp_m22 n (transpose_m22 M).
Proof.
  intros n M.
  induction M as [x11 x12 x21 x22].
  induction n as [ | n' IHn'].

  rewrite -> unfold_exp_m22_O.
  unfold transpose_m22 at 2.
  rewrite -> unfold_exp_m22_O.
  unfold I.
  unfold transpose_m22.
  reflexivity.

  unfold transpose_m22 at 2.
  rewrite ->2 unfold_exp_m22_S.
  rewrite -> transposition_distr_over_mul.
  rewrite -> IHn'.
  unfold transpose_m22.
  rewrite -> about_exp_m22_S.
  reflexivity.
Qed.

(*
15. Exercise 40
 *)

Proposition exponentiation_M22_1011':
  forall (n : nat),
    exp_m22 n (M22 1 0 1 1) = M22 1 0 n 1.
Proof.
  intro n.
  rewrite <- (transposition_involutive (M22 1 0 n 1)).
  rewrite <- (transposition_involutive (M22 1 0 1 1)).  
  unfold transpose_m22 at 2.
  unfold transpose_m22 at 3.
  rewrite <- (exponentiation_M22_1101 n).
  rewrite -> transp_and_exp_commutative.
  reflexivity.
Qed.

(*
16. Exercise 25. 
 *)
Definition F:= M22 1 1 1 0. 
Compute (exp_m22 0 F). (* M22 1 0 0 1 *)
Compute (exp_m22 1 F). (* M22 1 1 1 0 *)
Compute (exp_m22 2 F). (* M22 2 1 1 1 *)
Compute (exp_m22 3 F). (* M22 3 2 2 1 *)
Compute (exp_m22 4 F). (* M22 5 3 3 2 *)
Compute (exp_m22 5 F). (* M22 8 5 5 3 *)
Compute (exp_m22 6 F). (* M22 13 8 8 5 *)
Compute (exp_m22 7 F). (* M22 21 13 13 8 *)
Compute (exp_m22 8 F). (* M22 34 21 21 13 *)


Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).


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

Fixpoint fib (n: nat) : nat:=
  match n with
  | 0 => O
  | S n' => match n' with
            | O => 1
            | S n'' => fib n' + fib n''
            end
  end.

Compute (test_fib fib).
  
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

Proposition powers_of_F:
  forall (n : nat),
    exp_m22 (S n) F = M22 (fib (S (S n)))
                         (fib (S n))
                         (fib (S n))
                         (fib n).
Proof.
  intro n.
  induction n as [ | n' IHn'].

  unfold exp_m22.
  rewrite -> I_neutral_mul_m22_l.
  unfold F.
  unfold fib.
  rewrite -> Nat.add_0_r.
  reflexivity.

  rewrite -> unfold_exp_m22_S.
  rewrite -> IHn'.
  unfold F.
  unfold mul_m22.
  rewrite ->3 Nat.mul_1_r.
  rewrite ->2 Nat.mul_0_r.
  rewrite ->2 Nat.add_0_r.

  rewrite ->2 unfold_fib_SSn.
  reflexivity.
Qed.

Proposition fibonacci_addition_of_powers_of_F:
  forall (n : nat),
    add_m22 (exp_m22 n F) (exp_m22 (S n) F) = (exp_m22 (S (S n)) F). 
Proof.
  intro n.
  induction n as [ | n' IHn'].

  unfold F.
  unfold exp_m22.
  rewrite -> I_neutral_mul_m22_l.
  unfold mul_m22.
  unfold I.
  unfold add_m22.
  rewrite ->2 Nat.mul_0_r.
  rewrite -> Nat.mul_0_l.
  rewrite ->2 Nat.add_0_r.
  rewrite -> Nat.add_0_l.
  rewrite -> Nat.mul_1_r.
  rewrite -> Nat.add_1_r.
  reflexivity.
  
  rewrite ->3 powers_of_F.
  unfold add_m22.
  rewrite -> (Nat.add_comm (fib (S (S n'))) (fib (S (S (S n'))))).
  rewrite <- (unfold_fib_SSn (S (S n'))).
  rewrite -> (Nat.add_comm (fib (S n')) (fib (S (S n')))).
  rewrite <- (unfold_fib_SSn (S n')).
  rewrite -> (Nat.add_comm (fib n') (fib (S n'))).
  rewrite <- (unfold_fib_SSn n').
  reflexivity.
Qed.  


  (*
 X * implement Definition 9 (i.e., the multiplication of 2*2-matrices),

 X * implement the addition of 2*2-matrices

 X * implement Definitions 11 and 13,

 X * prove Properties 10 and 12,

 X * formalize Proposition 14 and its proof in Coq,

 X * implement Definition 27,

 X * solve Exercise 28,

 X * formalize Proposition 29 and its proof in Coq,

 X * solve Exercise 31,

 X * implement Corollary 32,

 X * solve Exercise 34,

 X * implement Definition 35,

 X * prove Property 36,

 X * formalize Proposition 37 and its proof in Coq,

 X * formalize Proposition 38 and its proof in Coq,

 X * solve Exercise 40, and to

 X * solve Exercise 25.

 X Subsidiary question for Exercise 25:
   characterize the result of adding F^n and F^(n+1), for any n : nat
*)

(* ********** *)

(* end of week-15_two-by-two-matrices.v *)
