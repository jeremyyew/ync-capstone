(* week-04_equational-reasoning-about-arithmetical-functions.v *)
(* FPP 2019 - YSC3236 2019-2020, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Corrected version of 05 Sep 2019 *)
(* Version of 10 Sep 2019 *)

(* ********** *)

(* [...] *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Two implementations of the addition function *)

(* ***** *)

(* Unit tests *)

Definition test_add (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 1)
  &&
  (candidate 1 0 =n= 1)
  &&
  (candidate 1 1 =n= 2)
  &&
  (candidate 1 2 =n= 3)
  &&
  (candidate 2 1 =n= 3)
  &&
  (candidate 2 2 =n= 4)
  (* etc. *)
  .

(* ***** *)

(* Recursive implementation of the addition function *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
  | O =>
    j
  | S i' =>
    S (add_v1 i' j)
  end.

Compute (test_add add_v1).

Lemma fold_unfold_add_v1_O :
  forall j : nat,
    add_v1 O j =
    j.
Proof.
  fold_unfold_tactic add_v1.
Qed.

Lemma fold_unfold_add_v1_S :
  forall i' j : nat,
    add_v1 (S i') j =
    S (add_v1 i' j).
Proof.
  fold_unfold_tactic add_v1.
Qed.

(* ***** *)

(* Tail-recursive implementation of the addition function *)

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v2 i' (S j)
  end.

Compute (test_add add_v2).

Lemma fold_unfold_add_v2_O :
  forall j : nat,
    add_v2 O j =
    j.
Proof.
  fold_unfold_tactic add_v2.
Qed.

Lemma fold_unfold_add_v2_S :
  forall i' j : nat,
    add_v2 (S i') j =
    add_v2 i' (S j).
Proof.
  fold_unfold_tactic add_v2.
Qed.

(* ********** *)

(* Equivalence of add_v1 and add_v2 *)

(* ***** *)

(* The master lemma: *)

Lemma about_add_v2 :
  forall i j : nat,
    add_v2 i (S j) = S (add_v2 i j).
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v2_O j).
    exact (fold_unfold_add_v2_O (S j)).

  - intro j.
    rewrite -> (fold_unfold_add_v2_S i' (S j)).
    rewrite -> (fold_unfold_add_v2_S i' j).
    Check (IHi' (S j)).
    exact (IHi' (S j)).
Qed.

(* ***** *)

(* The main theorem: *)

Theorem equivalence_of_add_v1_and_add_v2 :
  forall i j : nat,
    add_v1 i j = add_v2 i j.
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v2_O j).
    exact (fold_unfold_add_v1_O j).

  - intro j.
    rewrite -> (fold_unfold_add_v1_S i' j).
    rewrite -> (fold_unfold_add_v2_S i' j).
    rewrite -> (IHi' j).
    symmetry.
    exact (about_add_v2 i' j).
Qed.

(* ********** *)

(* Neutral (identity) element for addition *)

(* ***** *)

Property O_is_left_neutral_wrt_add_v1 :
  forall y : nat,
    add_v1 0 y = y.
Proof.
  
  intro y.
  rewrite (fold_unfold_add_v1_O y).
  reflexivity.  

Qed.

(* ***** *)

Property O_is_left_neutral_wrt_add_v2 :
  forall y : nat,
    add_v2 0 y = y.
Proof.
  intro y.
  unfold add_v2.
  reflexivity.
Qed.




  (******)
(*Exercise 7*)
  
  
Property O_is_right_neutral_wrt_add_v2 :
  forall x : nat,
    add_v2 x 0 = x.
Proof.
  intro x.
  induction x as [ | x' IHx'].

  - Check (fold_unfold_add_v2_O 0).
    exact (fold_unfold_add_v2_O 0).

  - rewrite -> (fold_unfold_add_v2_S x' 0).
    Check (about_add_v2 x' 0).
    rewrite -> (about_add_v2 x' 0).
    rewrite -> (IHx').
    reflexivity.
Qed.



(* ********** *)
(* ***** *)
(* Exercise 11 *)

Property add_v2_is_commutative :
  forall x y : nat,
    add_v2 x y = add_v2 y x.
Proof.
  intro x.
  induction x as [ | x' IHx'].
  
  - intro y.
   rewrite -> (O_is_left_neutral_wrt_add_v2 y).
   rewrite -> (O_is_right_neutral_wrt_add_v2 y).
   reflexivity.
   
  - intro y.
    Check(fold_unfold_add_v2_S x' y).
    rewrite -> (fold_unfold_add_v2_S x' y).
    rewrite -> (IHx' (S y)).
    rewrite ->(fold_unfold_add_v2_S y x').
    reflexivity.
Qed.

(* Associativity of addition *)

(* ***** *)


(* ***** *)
(*Exercise 9*)

Property add_v2_is_associative :
  forall x y z : nat,
    add_v2 x (add_v2 y z) = add_v2 (add_v2 x y) z.
Proof.
  intro x.
  induction x as [| x' IHx'].

  * intros y z.
    Check (O_is_left_neutral_wrt_add_v2 (add_v2 y z)).
    rewrite -> (O_is_left_neutral_wrt_add_v2 (add_v2 y z)).
    rewrite -> (O_is_left_neutral_wrt_add_v2 y).
    reflexivity.


  * intros y z. 
    Check (fold_unfold_add_v2_S x' (add_v2 y z)).
    rewrite -> (fold_unfold_add_v2_S x' (add_v2 y z)).
    Check (about_add_v2).
    Check (about_add_v2 x' (add_v2 y z)).
    rewrite -> (about_add_v2 x' (add_v2 y z)).
    rewrite -> (add_v2_is_commutative (S x') y).
    rewrite -> (about_add_v2 y x').
    rewrite -> (add_v2_is_commutative (S(add_v2 y x')) z).
    rewrite -> (about_add_v2 z (add_v2 y x')).
    rewrite -> (add_v2_is_commutative z (add_v2 y x')).
    rewrite -> (add_v2_is_commutative y x').
    rewrite -> (IHx' y z).
    reflexivity.
Qed.



(* ********** *)

(* Commutativity of addition *)

(* ***** *)


(* ********** *)

(* Four implementations of the multiplication function *)

(* ***** *)

(* Unit tests *)

Definition test_mul (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 0)
  &&
  (candidate 1 0 =n= 0)
  &&
  (candidate 1 1 =n= 1)
  &&
  (candidate 1 2 =n= 2)
  &&
  (candidate 2 1 =n= 2)
  &&
  (candidate 2 2 =n= 4)
  &&
  (candidate 2 3 =n= 6)
  &&
  (candidate 3 2 =n= 6)
  &&
  (candidate 6 4 =n= 24)
  &&
  (candidate 4 6 =n= 24)
  (* etc. *)
  .

(* ***** *)

(* Recursive implementation of the multiplication function, using add_v1 *)

Fixpoint mul_v11 (x y : nat) : nat :=
  match x with
  | O =>
    O
  | S x' =>
    add_v1 (mul_v11 x' y) y
  end.

Compute (test_mul mul_v11).

Lemma fold_unfold_mul_v11_O :
  forall y : nat,
    mul_v11 O y =
    O.
Proof.
  fold_unfold_tactic mul_v11.
Qed.

Lemma fold_unfold_mul_v11_S :
  forall x' y : nat,
    mul_v11 (S x') y =
    add_v1 (mul_v11 x' y) y.
Proof.
  fold_unfold_tactic mul_v11.
Qed.

(* ***** *)

(* Recursive implementation of the multiplication function, using add_v2 *)

Fixpoint mul_v12 (x y : nat) : nat :=
  match x with
  | O =>
    O
  | S x' =>
    add_v2 (mul_v12 x' y) y
  end.

Compute (test_mul mul_v11).

Lemma fold_unfold_mul_v12_O :
  forall y : nat,
    mul_v12 O y =
    O.
Proof.
  fold_unfold_tactic mul_v12.
Qed.

Lemma fold_unfold_mul_v12_S :
  forall x' y : nat,
    mul_v12 (S x') y =
    add_v2 (mul_v12 x' y) y.
Proof.
  fold_unfold_tactic mul_v12.
Qed.

(* ***** *)

(* Tail-recursive implementation of the multiplication function, using add_v1
Exercise 14 *)

Fixpoint mul_v21_aux (x y a: nat) : nat :=
  match x with
  | 0 =>
    a
  | S x' =>
    mul_v21_aux x' y (add_v1 y a)
  end.

Definition mul_v21 (x y : nat) : nat := mul_v21_aux x y 0.

Compute (test_mul mul_v21).



Lemma fold_unfold_mul_v21_aux_O :
  forall y a : nat,
    mul_v21_aux O y a =
    a.
Proof.
  fold_unfold_tactic mul_v21_aux.
Qed.


Lemma fold_unfold_mul_v21_aux_S :
  forall x' y a: nat,
    mul_v21_aux (S x') y a =
    mul_v21_aux x' y (add_v1 y a).
Proof.
  fold_unfold_tactic mul_v21_aux. 
Qed.




(* ***** *)

(* Tail-recursive implementation of the multiplication function, using add_v2
Exercise 15 *)

Fixpoint mul_v22_aux (x y a: nat) : nat :=
  match x with
  | 0 =>
    a
  | S x' =>
    mul_v22_aux x' y (add_v2 y a)
  end.

Definition mul_v22 (x y : nat) : nat := mul_v22_aux x y 0.


Compute (test_mul mul_v22).




Lemma fold_unfold_mul_v22_aux_O :
  forall y a: nat,
    mul_v22_aux O y a=
    a.
Proof.
  fold_unfold_tactic mul_v22_aux.
Qed.


Lemma fold_unfold_mul_v22_aux_S :
  forall x' y a: nat,
    mul_v22_aux (S x') y a =
    mul_v22_aux x' y (add_v2 y a).
Proof.
  fold_unfold_tactic mul_v22_aux.
Qed.

(* ********** *)

(* Equivalence of mul_v11, mul_v12, mul_v21, and mul_v22 
Exercise 16*)

(* ***** *)

Theorem equivalence_of_mul_v11_and_mul_v12 :
  forall i j : nat,
    mul_v11 i j = mul_v12 i j.
Proof.
  intro i.
  induction i as [|i' IHi'].

  * intro j.
    rewrite -> (fold_unfold_mul_v12_O j).
    exact (fold_unfold_mul_v12_O j).

  * intro j.
    rewrite -> (fold_unfold_mul_v11_S i' j).
    rewrite -> (fold_unfold_mul_v12_S i' j).
    rewrite -> (IHi' j).
    symmetry.
    Check (equivalence_of_add_v1_and_add_v2 (mul_v12 i' j) j).
    rewrite -> (equivalence_of_add_v1_and_add_v2 (mul_v12 i' j) j).
    reflexivity.
Qed.

Lemma about_mul_v22_aux :
  forall x y a : nat,
    mul_v22_aux x y a =
    add_v2 a (mul_v22_aux x y 0).
Proof.
  intro x.
  induction x as [|x' IHx'].

  * intros y a.
    rewrite -> (fold_unfold_mul_v22_aux_O y a).
    rewrite -> (fold_unfold_mul_v22_aux_O y 0).
    rewrite -> (O_is_right_neutral_wrt_add_v2 a).
    reflexivity.

  * intros y a.
    rewrite -> (fold_unfold_mul_v22_aux_S x' y a).
    rewrite -> (fold_unfold_mul_v22_aux_S x' y 0).
    rewrite -> (IHx' y (add_v2 y a)).
    rewrite -> (IHx' y (add_v2 y 0)).
    rewrite -> (O_is_right_neutral_wrt_add_v2 y).
    rewrite -> (add_v2_is_commutative y a).
    Check (add_v2_is_associative).
    rewrite -> (add_v2_is_associative a y).
    reflexivity.
Qed.


Lemma equivalence_of_mul_v21_aux_and_mul_v22_aux :
  forall i j a : nat,
    mul_v21_aux i j a = mul_v22_aux i j a.
Proof.
  intro i.
  induction i as [|i' IHi'].
  

  * intros j a.
    rewrite -> (fold_unfold_mul_v21_aux_O j a).
    rewrite -> (fold_unfold_mul_v22_aux_O j a).
    reflexivity.

  * intros j a.
    rewrite -> (fold_unfold_mul_v21_aux_S i' j a).
    rewrite -> (fold_unfold_mul_v22_aux_S i' j a).
    Check (equivalence_of_add_v1_and_add_v2).
    rewrite -> (equivalence_of_add_v1_and_add_v2 j a).
    rewrite -> (IHi' j (add_v2 j a)).
    reflexivity.
Qed.

Theorem equivalence_of_mul_v21_and_mul_v22 :
  forall i j : nat,
    mul_v21 i j = mul_v22 i j.
Proof.
  unfold mul_v22.
  unfold mul_v21.
  intros i j.
  Check (equivalence_of_mul_v21_aux_and_mul_v22_aux i j 0).
  exact (equivalence_of_mul_v21_aux_and_mul_v22_aux i j 0).
Qed.




(* end of week-04_equational-reasoning-about-arithmetical-functions.v *)
