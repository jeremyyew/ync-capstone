(* week-05_mystery-functions.v *)
(* FPP 2019 - YSC3236 2019-2020, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 10 Sep 2019 *)

(* ********** *)

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

Definition beq_nat_nat (p1 p2 : nat * nat) : bool :=
  match p1 with
  | (n11, n12) =>
    match p2 with
    | (n21, n22) =>
      (n11 =n= n21) && (n12 =n= n22)
    end
  end.

Notation "A =nn= B" :=
  (beq_nat_nat A B) (at level 70, right associativity).
         
(* ********** *)

Definition specification_of_mystery_function_00 (mf : nat -> nat) :=
  mf 0 = 1 /\ forall i j : nat, mf (S (i + j)) = mf i + mf j.

Proposition there_is_at_most_one_mystery_function_00 :
  forall f g : nat -> nat,
    specification_of_mystery_function_00 f ->
    specification_of_mystery_function_00 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_00.
  intros [H_f_O H_f_S] [H_g_O H_g_S].
  intro n.
  induction n as [ | n' IHn'].

  - rewrite -> H_g_O.
    exact H_f_O.

  - rewrite <- (Nat.add_0_l n').
    rewrite -> (H_f_S 0 n').
    rewrite -> (H_g_S 0 n').
    rewrite -> H_f_O.
    rewrite -> H_g_O.
    rewrite -> IHn'.
    reflexivity.
Qed.

Definition unit_test_for_mystery_function_00a (mf : nat -> nat) :=
  (mf 0 =n= 1) (* etc. *).

Definition unit_test_for_mystery_function_00b (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) (* etc. *).

Definition unit_test_for_mystery_function_00c (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) (* etc. *).

Definition unit_test_for_mystery_function_00d (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) && (mf 3 =n= 4)
  (* etc. *).

Definition mystery_function_00 := S.

Definition less_succinct_mystery_function_00 (n : nat) : nat :=
  S n.

Compute (unit_test_for_mystery_function_00d mystery_function_00).

Theorem there_is_at_least_one_mystery_function_00 :
  specification_of_mystery_function_00 mystery_function_00.
Proof.
  unfold specification_of_mystery_function_00, mystery_function_00.
  split.
  - reflexivity.
  - intros i j.
    rewrite -> plus_Sn_m.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Definition mystery_function_00_alt := fun (n : nat) => n + 1.

Theorem there_is_at_least_one_mystery_function_00_alt :
  specification_of_mystery_function_00 mystery_function_00_alt.
Proof.
Abort.

Theorem soundness_of_the_unit_test_function_for_mystery_function_00 :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00c mf = true.
Proof.
  unfold specification_of_mystery_function_00.
  unfold unit_test_for_mystery_function_00c.
  intros mf [H_O H_S].
  (* Goal: (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> H_O.
  (* Goal: (1 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> (Nat.eqb_refl 1).
  (* Goal: true && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> (andb_true_l (mf 1 =n= 2)).
  (* Goal: (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  (* etc. *)
  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  rewrite -> (Nat.add_1_l 1).
  Check (Nat.eqb_refl 2).
  rewrite -> (Nat.eqb_refl 2).
  rewrite -> (andb_true_l (mf 2 =n= 3)).
  Check (Nat.add_1_l 1).
  rewrite <- (Nat.add_1_l 1) at 1.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  rewrite -> (H_S 0 1).
  rewrite -> H_O.
  rewrite <- (Nat.add_1_l 0) at 2.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  rewrite -> (Nat.add_1_l 1).
  rewrite -> (Nat.add_1_l 2).
  exact (Nat.eqb_refl 3).
Qed.

Theorem soundness_of_the_unit_test_function_for_mystery_function_00b :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00b mf = true.
Proof.
  unfold specification_of_mystery_function_00,
         unit_test_for_mystery_function_00b.
  intros mf [H_O H_S].
  (* Goal: (mf 0 =n= 1) && (mf 1 =n= 2) = true *)
  rewrite -> H_O.
  (* Goal: (1 =n= 1) && (mf 1 =n= 2) = true *)
  rewrite -> (Nat.eqb_refl 1).
  (* Goal: true && (mf 1 =n= 2) = true *)
  rewrite -> (andb_true_l (mf 1 =n= 2)).
  (* Goal: (mf 1 =n= 2) = true *)
  (* etc. *)
  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  Check (Nat.add_1_r 0).
  rewrite -> (Nat.add_1_r 0).
  Check (Nat.eqb_refl 2).
  exact (Nat.eqb_refl 2).
Qed.

Theorem soundness_of_the_unit_test_function_for_mystery_function_00_with_Search :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00b mf = true.
Proof.
  unfold specification_of_mystery_function_00,
         unit_test_for_mystery_function_00b.
  intros mf [H_O H_S].

  rewrite -> H_O.
  Search (beq_nat _  _ = true).
  Check (Nat.eqb_refl 1).
  rewrite -> (Nat.eqb_refl 1).
  Search (true && _ = _).
  Check (andb_true_l (mf 1 =n= 2)).
  rewrite -> (andb_true_l (mf 1 =n= 2)).

  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  Check (Nat.add_1_r 0).
  rewrite -> (Nat.add_1_r 0).
  Check (Nat.eqb_refl 2).
  exact (Nat.eqb_refl 2).
Qed.

(* ********** *)

(* {SPECIFICATION_OF_MYSTERY_FUNCTION_11} *)
Definition specification_of_mystery_function_11 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i j : nat,
    mf (i + j) = mf i + 2 * i * j + mf j.

Theorem there_is_at_most_one_mystery_function_11:
  forall f g : nat -> nat,
    specification_of_mystery_function_11 f ->
    specification_of_mystery_function_11 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_11.
  intros [H_f_1 H_f_S] [H_g_1 H_g_S].
  intro n.
  induction n as [ | n' IHn'].

  - assert (H_tmp := H_f_S 0 0).
    rewrite -> (Nat.add_0_r 0) in H_tmp.
    rewrite -> (Nat.mul_0_r (2 * 0)) in H_tmp.
    rewrite -> (Nat.add_0_r (f 0)) in H_tmp.
    rewrite <- (Nat.add_0_r (f 0)) in H_tmp at 1.
    (* apply plus_reg_l in H_tmp. *)
    (* Yikes: *)
    Check plus_reg_l.
    Check (plus_reg_l 0 (f 0) (f 0)).
    apply (plus_reg_l 0 (f 0) (f 0)) in H_tmp.
    (* *)
    rewrite <- H_tmp.
    clear H_tmp.
    assert (H_tmp := H_g_S 0 0).
    rewrite -> (Nat.add_0_r 0) in H_tmp.
    rewrite -> (Nat.mul_0_r (2 * 0)) in H_tmp.
    rewrite -> (Nat.add_0_r (g 0)) in H_tmp.
    rewrite <- (Nat.add_0_r (g 0)) in H_tmp at 1.
    apply plus_reg_l in H_tmp.
    rewrite <- H_tmp.
    clear H_tmp.
    reflexivity.

  - Search (S _ = _).
    assert (H_tmp := plus_n_Sm n' 0).
    rewrite -> (Nat.add_0_r n') in H_tmp.
    rewrite -> H_tmp.
    rewrite -> (H_f_S n' 1).
    rewrite -> (H_g_S n' 1).
    rewrite -> IHn'.
    rewrite -> H_f_1.
    rewrite -> H_g_1.
    reflexivity.
Qed.

Definition unit_test_for_mystery_function_11 (mf : nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 1) && (mf 2 =n= 4) && (mf 3 =n= 9)
(* etc. *).

Definition mystery_function_11 (n : nat) : nat :=
  n * n.

Compute (unit_test_for_mystery_function_11 mystery_function_11).

Theorem there_is_at_least_one_mystery_function_11 :
  specification_of_mystery_function_11 mystery_function_11.
Proof.
  unfold specification_of_mystery_function_11, mystery_function_11.
  split.
  - rewrite -> (Nat.mul_1_r 1).
    reflexivity.

  - intros i j.
    rewrite -> (Nat.mul_add_distr_r i j (i + j)).
    rewrite -> (Nat.mul_add_distr_l i i j).
    rewrite -> (Nat.mul_add_distr_l j i j).
    rewrite -> BinInt.ZL0.
    rewrite -> (Nat.mul_add_distr_r 1 1 i).
    rewrite -> Nat.mul_1_l.
    rewrite -> (Nat.mul_add_distr_r i i j).
    rewrite -> (Nat.mul_comm j i).
    rewrite -> (Nat.add_assoc (i * i + i * j) (i * j) (j * j)).
    rewrite -> (Nat.add_assoc (i * i) (i * j) (i * j)).
    reflexivity.
Qed.

(* ***** *)

Definition specification_of_mystery_function_04 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  forall n' : nat,
    mf (S n') = mf n' + S (2 * n').

Lemma equivalence_of_successor_and_add_one : (* Ahem, Check Nat.add_1_r. *)
  forall n : nat,
    S n = n + 1.
Proof.
  intro n.
  rewrite <- (Nat.add_0_r n) at 1.
  rewrite -> (plus_n_Sm n 0).
  reflexivity.
Qed.

Lemma equivalence_of_times_two_and_add_itself :
  forall n : nat,
    2 * n = n + n.
Proof.
  intro n.
  rewrite -> BinInt.ZL0.
  rewrite -> (Nat.mul_add_distr_r 1 1 n).
  rewrite -> (Nat.mul_1_l n).
  reflexivity.
Qed.

Lemma distributive_law_l_r :
  forall a b c d : nat,
    (a + b) * (c + d) = a * c + a * d + b * c + b * d.
Proof.
  intros a b c d.
  rewrite -> Nat.mul_add_distr_r.
  rewrite -> Nat.mul_add_distr_l.
  rewrite -> (Nat.mul_add_distr_l b c d).
  rewrite -> (Nat.add_assoc (a * c + a * d) (b * c) (b * d)).
  reflexivity.
Qed.

Theorem there_is_at_most_one_mystery_function_04:
  forall f g : nat -> nat,
    specification_of_mystery_function_04 f ->
    specification_of_mystery_function_04 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_04.
  intros [H_f_O H_f_S] [H_g_O H_g_S].
  intro n.
  induction n as [ | n' IHn'].

  - rewrite -> H_g_O.
    exact (H_f_O).

  - rewrite -> (H_f_S n').
    rewrite -> (H_g_S n').
    rewrite -> IHn'.
    reflexivity.
Qed.    

Definition unit_test_for_mystery_function_04 (mf : nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 1) && (mf 2 =n= 4) && (mf 3 =n= 9)
(* etc. *).

Definition mystery_function_04 (n : nat) : nat :=
  n * n.

Compute (unit_test_for_mystery_function_04 mystery_function_04).

Theorem there_is_at_least_one_mystery_function_04 :
  specification_of_mystery_function_04 mystery_function_04.
Proof.
  unfold specification_of_mystery_function_04, mystery_function_04.
  split.
  - rewrite -> (Nat.mul_0_r 0).
    reflexivity.

  - intros n'.
    rewrite -> (equivalence_of_times_two_and_add_itself n').
    rewrite -> equivalence_of_successor_and_add_one.
    rewrite -> (equivalence_of_successor_and_add_one (n' + n')).
    rewrite -> distributive_law_l_r.
    rewrite -> (Nat.mul_1_r n').
    rewrite -> (Nat.mul_1_l n').
    rewrite -> (Nat.mul_1_l 1).
    rewrite -> (Nat.add_assoc (n' * n') (n' + n')  1).
    rewrite -> (Nat.add_assoc (n' * n') n' n').
    reflexivity.
Qed.

(* ***** *)

Definition specification_of_mystery_function_15 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (S x, y * S x).

Theorem there_is_at_most_one_mystery_function_15:
  forall f g : nat -> nat * nat,
    specification_of_mystery_function_15 f ->
    specification_of_mystery_function_15 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_15.
  intros [H_f_O H_f_S] [H_g_O H_g_S].
  intro n.
  induction n as [ | n' IHn'].

  - rewrite -> H_g_O.
    exact (H_f_O).

  - rewrite -> H_f_S.
    rewrite -> H_g_S.
    rewrite -> IHn'.
    reflexivity.
Qed.

Definition unit_test_for_mystery_function_15 (mf : nat -> nat * nat) :=
  (mf 0 =nn= (0, 1)) && (mf 1 =nn= (1, 1)) && (mf 2 =nn= (2, 2)) && (mf 3 =nn= (3, 6)).

(* etc. *)

Fixpoint fac (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => (fac n') * n
  end.
                          
Definition mystery_function_15 (n : nat) : nat * nat :=
  (n, fac n).

Compute (unit_test_for_mystery_function_15 mystery_function_15).

Theorem there_is_at_least_one_mystery_function_15:
  specification_of_mystery_function_15 mystery_function_15.
Proof.
  unfold specification_of_mystery_function_15, mystery_function_15.
  split.
  - unfold fac.
    reflexivity.

  - intro n'.
    unfold fac.
    fold fac.
    reflexivity.
Qed.
    (* ***** *)

Definition specification_of_mystery_function_16 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (y, x + y).

Theorem there_is_at_most_one_mystery_function_16:
  forall f g : nat -> nat * nat,
    specification_of_mystery_function_16 f ->
    specification_of_mystery_function_16 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_16.
  intros [H_f_O H_f_S] [H_g_O H_g_S].
  intro n.
  induction n as [ | n' IHn'].

  - rewrite -> H_g_O.
    exact (H_f_O).

  - rewrite -> H_f_S.
    rewrite -> H_g_S.
    rewrite -> IHn'.
    reflexivity.
Qed.

Definition unit_test_for_mystery_function_16 (mf : nat -> nat * nat) :=
  (mf 0 =nn= (0, 1)) && (mf 1 =nn= (1, 1)) && (mf 2 =nn= (1, 2)) && (mf 3 =nn= (2, 3)).

Fixpoint fib (n : nat) : nat :=
  match n with
  | O => 0
  | (S n') =>
    match n' with
    | O => 1
    | (S n'') => (fib n'') + (fib n')
    end
  end.

Definition mystery_function_16 (n : nat) : nat * nat :=
  (fib n, fib (S n)).

Compute (unit_test_for_mystery_function_16 mystery_function_16).

Theorem there_is_at_least_one_mystery_function_16:
  specification_of_mystery_function_16 mystery_function_16.
Proof.
  unfold specification_of_mystery_function_16, mystery_function_16.
  split.
  - unfold fib.
    reflexivity.

  - intro n'.
    unfold fib.
    fold fib.
    reflexivity.
Qed.

(* ***** *)

Lemma triple_induction (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  P 2 ->
  (forall n, P n -> P (S n) -> P (S (S n)) -> P (S (S (S n)))) ->
  forall n, P n.
Proof.
  intros H0 H1 H2 Hstep n.
  enough (P n /\ P (S n) /\ P (S (S n))) as [H [H_S H_SS]].
  - exact H.
  - induction n as [ | n [IH IH_S]]. 
    * exact (conj H0 (conj H1 H2)).
    * destruct IH_S as [IH_S_1 IH_S_2].
      + split.
        ++ exact IH_S_1.
        ++ split.
           +++ exact IH_S_2.
           +++ exact ((Hstep n) IH IH_S_1 IH_S_2).
Qed.

Definition specification_of_mystery_function_17 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall p q : nat,
    mf (S (p + q)) = mf (S p) * mf (S q) + mf p * mf q.


Theorem there_is_at_most_one_mystery_function_17:
  forall f g : nat -> nat,
    specification_of_mystery_function_17 f ->
    specification_of_mystery_function_17 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_17.
  intros [H_f_O [H_f_1 [H_f_2 H_f_S]]] [H_g_O [H_g_1 [H_g_2 H_g_S]]].
  intro n.
  induction n using triple_induction.
  
  - rewrite -> H_g_O.
    exact (H_f_O).

  - rewrite -> H_g_1.
    exact (H_f_1).

  - rewrite -> H_g_2.
    exact (H_f_2).

  - assert (H_tmp := H_f_S (n + 1) 1).
    Search (2 = 1 + 1).
    rewrite -> (Nat.add_1_r n) in H_tmp.
    rewrite -> (Nat.add_1_r (S n)) in H_tmp.
    rewrite -> H_tmp.
    rewrite -> H_f_2. 
    rewrite -> H_f_1.
    clear H_tmp.
    assert (H_tmp := H_g_S (n + 1) 1).
    Search (2 = 1 + 1).
    rewrite -> (Nat.add_1_r n) in H_tmp.
    rewrite -> (Nat.add_1_r (S n)) in H_tmp.
    rewrite -> H_tmp.
    rewrite -> H_g_2. 
    rewrite -> H_g_1.
    rewrite -> IHn1.
    rewrite -> IHn0.
    reflexivity.
Qed.

Definition unit_test_for_mystery_function_17 (mf : nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 1) && (mf 2 =n= 1) && (mf 3 =n= 2)
(* etc. *).

Definition mystery_function_17 (n : nat) : nat :=
  fib n.

Compute (unit_test_for_mystery_function_17 mystery_function_17).

Theorem there_is_at_least_one_mystery_function_17 :
  specification_of_mystery_function_17 mystery_function_17.
Proof.
  unfold specification_of_mystery_function_17, mystery_function_17.
  split.
  { unfold fib.
    reflexivity.
  }
  split.
  { unfold fib.
    reflexivity.
  } 
  split.
  { unfold fib.
    exact (Nat.add_0_l 1).
  }
  intros p q.
  induction p as [ | p' IHp'].
 
  - (* an induction proof *)
Abort.

(* ***** *)

Definition specification_of_mystery_function_18 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall n''' : nat,
    mf n''' + mf (S (S (S n'''))) = 2 * mf (S (S n''')).

Theorem there_is_at_most_one_mystery_function_18:
  forall f g : nat -> nat,
    specification_of_mystery_function_18 f ->
    specification_of_mystery_function_18 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_18.
  intros [H_f_O [H_f_1 [H_f_2 H_f_S]]] [H_g_O [H_g_1 [H_g_2 H_g_S]]].
  intro n.
  induction n using triple_induction.
  
  - rewrite -> H_g_O.
    exact (H_f_O).

  - rewrite -> H_g_1.
    exact (H_f_1).

  - rewrite -> H_g_2.
    exact (H_f_2).

  - assert (H_tmp := H_f_S n).
    assert (H_tmp2 := H_g_S n).
    rewrite -> IHn1 in H_tmp.
    rewrite <- H_tmp2 in H_tmp.
    rewrite -> IHn in H_tmp.
    Search (_ + _ = _ + _ -> _).
    exact ((plus_reg_l (f (S (S (S n)))) (g (S (S (S n)))) (g n) ) H_tmp).
Qed.

Definition unit_test_for_mystery_function_18 (mf : nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 1) && (mf 2 =n= 1) && (mf 3 =n= 2)
(* etc. *).

Definition mystery_function_18 (n : nat) : nat :=
  fib n.

Compute (unit_test_for_mystery_function_18 mystery_function_18).

Theorem there_is_at_least_one_mystery_function_18 :
  specification_of_mystery_function_18 mystery_function_18.
Proof.
  unfold specification_of_mystery_function_18, mystery_function_18.
  split.
  { unfold fib.
    reflexivity.
  }
  split.
  { unfold fib.
    reflexivity.
  } 
  split.
  { unfold fib.
    exact (Nat.add_0_l 1).
  }
  intro n.
  induction n as [ | n' IHn'].
 
  - unfold fib. fold fib. 
    rewrite -> Nat.add_0_l.
    rewrite -> Nat.add_0_l.
    rewrite -> (Nat.mul_1_r 2).
    symmetry.
    exact BinInt.ZL0.

  - (* an induction proof *)
Abort.

(* ***** *)

Definition specification_of_mystery_function_03 (mf : nat -> nat -> nat) :=
  mf 0 0 = 0
  /\
  (forall i j: nat, mf (S i) j = S (mf i j))
  /\
  (forall i j: nat, S (mf i j) = mf i (S j)).

Theorem there_is_at_most_one_mystery_function_03:
  forall f g : nat -> nat -> nat,
    specification_of_mystery_function_03 f ->
    specification_of_mystery_function_03 g ->
    forall i j : nat,
      f i j = g i j.
Proof.
  intros f g.
  unfold specification_of_mystery_function_03.
  intros [H_f_O [H_f_S  H_f_S']] [H_g_O [H_g_S H_g_S']].
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    induction j as [ | j' IHj'].

    -- rewrite -> H_g_O.
       exact (H_f_O).
    -- rewrite <- (H_g_S' 0 j').
       rewrite <- (H_f_S' 0 j').
       rewrite <- IHj'.
       reflexivity.
  - intro j.
    rewrite -> (H_f_S i' j).
    rewrite -> (H_g_S i' j).
    rewrite -> IHi'.
    reflexivity.
Qed.

Definition unit_test_for_mystery_function_03 (mf : nat -> nat -> nat) :=
  (mf 0 0 =n= 0) && (mf 0 1 =n= 1) && (mf 1 0 =n= 1) && (mf 1 1 =n= 2) && (mf 1 2 =n= 3) && (mf 2 1 =n= 3) && (mf 2 2 =n= 4).

Fixpoint mystery_function_03 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => mystery_function_03 i' (S j)
  end.

Compute (unit_test_for_mystery_function_03 mystery_function_03).

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Lemma fold_unfold_mystery_function_03_O :
  forall j : nat,
   mystery_function_03 O j =
    j.
Proof.
  fold_unfold_tactic mystery_function_03.
Qed.

Lemma fold_unfold_mystery_function_03_S :
  forall i' j : nat,
    mystery_function_03 (S i') j =
    mystery_function_03 i' (S j).
Proof.
  fold_unfold_tactic mystery_function_03.
Qed.

Lemma about_mystery_function_03 :
  forall i j : nat,
    mystery_function_03 i (S j) = S (mystery_function_03 i j).
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_mystery_function_03_O j).
    exact (fold_unfold_mystery_function_03_O (S j)).

  - intro j.
    rewrite -> (fold_unfold_mystery_function_03_S i' (S j)).
    rewrite -> (fold_unfold_mystery_function_03_S i' j).
    Check (IHi' (S j)).
    exact (IHi' (S j)).
Qed.

Theorem there_is_at_least_one_mystery_function_03:
  specification_of_mystery_function_03 mystery_function_03.
Proof.
  unfold specification_of_mystery_function_03, mystery_function_03.
  split.
  - reflexivity.

  - split.
    -- unfold mystery_function_03.
       fold mystery_function_03.
       exact (about_mystery_function_03).

    -- unfold mystery_function_03.
       fold mystery_function_03.
       symmetry.
       apply (about_mystery_function_03 i j).
Qed.

(* ***** *)

Definition specification_of_mystery_function_42 (mf : nat -> nat) :=
  mf 1 = 42
  /\
  forall i j : nat,
    mf (i + j) = mf i + mf j.

Theorem there_is_at_most_one_mystery_function_42:
  forall f g : nat -> nat,
    specification_of_mystery_function_42 f ->
    specification_of_mystery_function_42 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_42.
  intros [H_f_1 H_f_S] [H_g_1 H_g_S].
  intro n.
  induction n as [ | n' IHn'].
  - assert (H_tmp := H_f_S 0 1).
    Search (0 + _ = _).
    rewrite -> (Nat.add_0_l 1) in H_tmp.
    rewrite -> H_f_1 in H_tmp.
    Search (_ + _ = _).
    rewrite <- (Nat.add_0_l 42) in H_tmp at 1.
    Search (_ + _ = _ + _).
    rewrite -> (Nat.add_cancel_r 0 (f 0) 42) in H_tmp.
    rewrite <- H_tmp.
    clear H_tmp.
    assert (H_tmp := H_g_S 0 1).
    rewrite -> (Nat.add_0_l 1) in H_tmp.
    rewrite -> H_g_1 in H_tmp.
    rewrite <- (Nat.add_0_l 42) in H_tmp at 1.
    rewrite -> (Nat.add_cancel_r 0 (g 0) 42) in H_tmp.
    rewrite <- H_tmp.
    reflexivity.
  - rewrite -> (equivalence_of_successor_and_add_one n').
    rewrite -> (H_f_S n' 1).
    rewrite -> H_f_1.
    rewrite -> (H_g_S n' 1).
    rewrite -> H_g_1.
    rewrite -> IHn'.
    reflexivity.    
Qed.

Definition unit_test_for_mystery_function_42 (mf : nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 42) && (mf 2 =n= 84) && (mf 3 =n= 126).

Definition mystery_function_42 (n : nat) : nat :=
  n * 42.

Compute (unit_test_for_mystery_function_42 mystery_function_42).

Theorem there_is_at_least_one_mystery_function_42:
  specification_of_mystery_function_42 mystery_function_42.
Proof.
  unfold specification_of_mystery_function_42, mystery_function_42.
  split.
  - exact (Nat.mul_1_l 42).
    
  - intros i j.
    Search ((_ + _) * _ = _ * _ + _ * _).
    exact (Nat.mul_add_distr_r i j 42).
Qed.

(* ***** *)

Definition specification_of_mystery_function_07 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf 0 j = j)
  /\
  (forall i : nat, mf i 0 = i)
  /\
  (forall i j k : nat, mf (i + k) (j + k) = (mf i j) + k).

Theorem there_is_at_most_one_mystery_function_07:
  forall f g : nat -> nat -> nat,
    specification_of_mystery_function_07 f ->
    specification_of_mystery_function_07 g ->
    forall i j : nat,
      f i j = g i j.
Proof.
  intros f g.
  unfold specification_of_mystery_function_07.
  intros [H_f_O_l [H_f_O_r H_f_S]] [H_g_O_l [H_g_O_r H_g_S]].
  intros i.
  induction i as [ | i' IHi'].
  - intro j.
    induction j as [ | j' IHj'].
    -- rewrite -> (H_g_O_l 0).
       exact (H_f_O_l 0).
    -- rewrite -> (H_g_O_l (S j')).
       exact (H_f_O_l (S j')).
  - intro j.
    induction j as [ | j' IHj'].
    -- rewrite -> (H_g_O_r (S i')).
       exact (H_f_O_r (S i')).
    -- rewrite -> (equivalence_of_successor_and_add_one i').
       rewrite -> (equivalence_of_successor_and_add_one j').
       rewrite -> (H_f_S i' j' 1).
       rewrite -> (H_g_S i' j' 1).
       rewrite -> IHi'.
       reflexivity.
  (*    
  Restart.

  intros f g.
  unfold specification_of_mystery_function_07.
  intros [H_f_O_l [H_f_O_r H_f_S]] [H_g_O_l [H_g_O_r H_g_S]].
  intros i.
  induction i as [ | i' IHi'].
  - intro j.
    rewrite -> (H_g_O_l).
    exact (H_f_O_l j).
  - intro j.
    assert (H_tmp := H_f_S i' (j-1) 1).
    rewrite <- (equivalence_of_successor_and_add_one i') in H_tmp.
    Search (_ = _ - 1).
    rewrite <- (equivalence_of_successor_and_add_one j) in H_tmp.
    assert (H_tmp' := (IHi' (j - 1))).
    rewrite -> Nat.add_0_r in H_tmp.
    rewrite -> Nat.add_0_r in H_tmp.
    rewrite -> Nat.add_0_r in H_tmp. *)
Qed.

Definition unit_test_for_mystery_function_07 (mf : nat -> nat -> nat) :=
  (mf 0 1 =n= 1) && (mf 1 0 =n= 1) && (mf 2 2 =n= 2) && (mf 2 6 =n= 6).

Definition mystery_function_07 (i j : nat) : nat :=
  Nat.max i j.

Compute (unit_test_for_mystery_function_07 mystery_function_07).

Theorem there_is_at_least_one_mystery_function_07:
  specification_of_mystery_function_07 mystery_function_07.
Proof.
  unfold specification_of_mystery_function_07, mystery_function_07.
  split.
  - intro j.
    exact (Nat.max_0_l j).
    
  - split.
    -- intro i.
       exact (Nat.max_0_r i).
    -- intros i j k.
       exact (Nat.add_max_distr_r i j k).
Qed.

(* ***** *)

Definition specification_of_mystery_function_08 (mf : nat -> nat -> bool) :=
  (forall j : nat, mf 0 j = true)
  /\
  (forall i : nat, mf (S i) 0 = false)
  /\
  (forall i j : nat, mf (S i) (S j) = mf i j).

Theorem there_is_at_most_one_mystery_function_08:
  forall f g : nat -> nat -> bool,
    specification_of_mystery_function_08 f ->
    specification_of_mystery_function_08 g ->
    forall i j : nat,
      f i j = g i j.
Proof.
  intros f g.
  unfold specification_of_mystery_function_08.
  intros [H_f_O_l [H_f_O_r H_f_S]] [H_g_O_l [H_g_O_r H_g_S]].
  intros i.
  induction i as [ | i' IHi'].
  - intro j.
    induction j as [ | j' IHj'].
    -- rewrite -> (H_g_O_l 0).
       exact (H_f_O_l 0).
    -- rewrite -> (H_g_O_l (S j')).
       exact (H_f_O_l (S j')).
  - intro j.
    induction j as [ | j' IHj'].
    -- rewrite -> (H_g_O_r i').
       exact (H_f_O_r i').
    -- rewrite -> (H_g_S i' j').
       rewrite -> (H_f_S i' j').
       rewrite -> (IHi' j').
       reflexivity.
Qed.

Definition unit_test_for_mystery_function_08 (mf : nat -> nat -> bool) :=
  (mf 0 0 =b= true) && (mf 1 0 =b= false) && (mf 0 1 =b= true) && (mf 2 6 =b= true) && (mf 6 6 =b= true).

Definition mystery_function_08 (i j : nat) : bool :=
  (Nat.min i j) =n= i.

Compute (unit_test_for_mystery_function_08 mystery_function_08).

Theorem there_is_at_least_one_mystery_function_08:
  specification_of_mystery_function_08 mystery_function_08.
Proof.
  unfold specification_of_mystery_function_08, mystery_function_08.
  split.
  - intro j.
    Search (Nat.min 0 _).
    rewrite -> (Nat.min_0_l j).
    Search (beq_nat _ _).
    exact (Nat.eqb_refl 0).
    
  - split.
    -- intro i.
    rewrite -> (equivalence_of_successor_and_add_one i) at 1.
    rewrite -> (Nat.min_0_r (i + 1)).
    Search (beq_nat _ _).
    assert (H_tmp := (Nat.neq_succ_0 i)).
    Search (_ <> _ -> _).
    apply (Nat.neq_sym (S i) 0) in H_tmp.
    Search (_ =n= _).
    apply (Nat.eqb_neq 0 (S i)).
    exact H_tmp.

    -- intros i j.
       Search(Nat.min).
       Search (beq_nat).
       rewrite <- (Nat.succ_min_distr i j).
       rewrite <- (Nat.add_1_l (Nat.min i j)).
       rewrite <- (Nat.add_1_l i).
       destruct (Nat.lt_ge_cases j i) as [ H_i_greater_j | H_i_smaller_eq_j ].
    * assert (H_tmp := Nat.lt_neq j i).
      assert (H_neq := H_tmp H_i_greater_j).
      clear H_tmp.
      apply Nat.lt_le_incl in H_i_greater_j.
      rewrite -> (Nat.min_r i j).
      ** assert (H_tmp := Nat.lt_neq i j).
         assert (H_tmp2 := (not_eq_S j i)).
         assert (H_neq_S := H_tmp2 H_neq).
         rewrite <- (Nat.add_1_l j) in H_neq_S.
         rewrite <- (Nat.add_1_l i) in H_neq_S.
         assert (H_tmp3 := Nat.eqb_neq (1 + j) (1 + i)).
         destruct H_tmp3 as [_ H_tmp3_right].
         rewrite -> (H_tmp3_right H_neq_S).
         symmetry.
         clear H_tmp2 H_neq_S H_tmp3_right.
         assert (H_tmp2 := Nat.eqb_neq j i).
         destruct H_tmp2 as [_ H_tmp2_right].
         exact (H_tmp2_right H_neq).
      ** exact H_i_greater_j.
    * rewrite -> ((Nat.min_l i j) H_i_smaller_eq_j).
      rewrite -> (Nat.eqb_refl i).
      exact (Nat.eqb_refl (1 + i)).
Qed.

(* ***** *)

Definition specification_of_mystery_function_23 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 0
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

Lemma zero_or_nonzero :
  forall n : nat,
  (n = 0) \/ (n <> 0).
Proof.
  intro n.
  induction n as [ | n' IHn'].

  - left.
    reflexivity.

  - right.
    exact (Nat.neq_succ_0 n').
Qed.
 
(* Master Lemma *)

Lemma pair_induction (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P (S n) -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros H0 H1 Hstep n.
  enough (P n /\ P (S n)) as [H H_S].
  + exact H.
  +  induction n as [ | n' [IHn' IHn'2]].

  * split.
    - exact H0.
    - exact H1.
  * split.
    - exact IHn'2.
    - exact (Hstep n' IHn' IHn'2).
Qed. 

Theorem there_is_at_most_one_mystery_function_23:
  forall f g : nat -> nat,
    specification_of_mystery_function_23 f ->
    specification_of_mystery_function_23 g ->
    forall n : nat,
      f n = g n.
Proof.
intros f g.
  unfold specification_of_mystery_function_23.
  intros [H_f_O [H_f_1 H_f_S]] [H_g_O [H_g_1 H_g_S]].
  intro n.
  induction n using pair_induction.

  - rewrite -> H_g_O.
    exact (H_f_O).
  - rewrite -> H_g_1.
    exact H_f_1.
  - rewrite -> (H_f_S n).
    rewrite -> (H_g_S n).
    rewrite -> IHn.
    reflexivity.
Qed.

Definition unit_test_for_mystery_function_23 (mf : nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 0) && (mf 2 =n= 1) && (mf 3 =n= 1)
(* etc. *).

Definition mystery_function_23 (n : nat) : nat :=
  n / 2.

Compute (unit_test_for_mystery_function_23 mystery_function_23).

Theorem there_is_at_least_one_mystery_function_23:
  specification_of_mystery_function_23 mystery_function_23.
Proof.
  unfold specification_of_mystery_function_23, mystery_function_23.
  split.

 - apply (Nat.div_0_l 2).
   exact (Nat.neq_succ_0 1).
 - split.
   apply (Nat.div_1_l 2).
   * exact Nat.lt_1_2.
   * intro n.
     rewrite <- (Nat.add_1_l n).
     rewrite <- (Nat.add_1_l (1 + n)).
     rewrite -> (Nat.add_assoc 1 1 n).
     rewrite <- BinInt.ZL0.
     rewrite <- (Nat.add_1_l (n / 2)).
     rewrite <- (Nat.mul_1_l 2) at 1.
     rewrite -> (Nat.div_add_l 1 2 n).
     ** reflexivity.
     ** exact (Nat.neq_succ_0 1).
Qed.
 
(* ***** *)

Definition specification_of_mystery_function_24 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\ forall n'' : nat,
      mf (S (S n'')) = S (mf n'').
(* (n + 1) / 2 *)
(* ***** *)

Theorem there_is_at_most_one_mystery_function_24:
  forall f g : nat -> nat,
    specification_of_mystery_function_24 f ->
    specification_of_mystery_function_24 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_24.
  intros [H_f_O [H_f_1 H_f_S]] [H_g_O [H_g_1 H_g_S]].

  assert (H_n : forall n : nat, f n = g n /\ f (S n) = g (S n)).
  { intro n.
    induction n as [ | n' [IHn' IHSn']].

    - split.

      -- rewrite -> H_f_O.
         rewrite -> H_g_O.
         reflexivity.

      -- rewrite -> H_f_1.
         rewrite -> H_g_1.
         reflexivity.

    - split.

      -- exact IHSn'.

      -- rewrite -> H_f_S.
         rewrite -> H_g_S.
         rewrite -> IHn'.
         reflexivity.
  }
  intro n.
  destruct (H_n n) as [ly _].
  exact ly.
Qed.
(*
  intros f g.
  unfold specification_of_mystery_function_24.
  intros [H_f_O [H_f_1 H_f_S]] [H_g_O [H_g_1 H_g_S]].
  intro n.
  induction n using pair_induction.

  - rewrite -> H_g_O.
    exact (H_f_O).
  - rewrite -> H_g_1.
    exact H_f_1.
  - rewrite -> (H_f_S n).
    rewrite -> (H_g_S n).
    rewrite -> IHn.
    reflexivity.
Qed.
*)

Definition unit_test_for_mystery_function_24 (mf : nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 1) && (mf 2 =n= 1) && (mf 3 =n= 2)
(* etc. *).

Definition mystery_function_24 (n : nat) : nat :=
  (n + 1) / 2.

Compute (unit_test_for_mystery_function_24 mystery_function_24).


Theorem there_is_at_least_one_mystery_function_24:
  specification_of_mystery_function_24 mystery_function_24.
Proof.
  unfold specification_of_mystery_function_24, mystery_function_24.
  split.

 - apply (Nat.div_0_l 2).
   exact (Nat.neq_succ_0 1).
 - split.
   * rewrite <- BinInt.ZL0.
     exact ((Nat.div_same 2) (Nat.neq_succ_0 1)).
   * intro n.
     rewrite <- (Nat.add_1_l n).
     rewrite <- (Nat.add_1_l (1 + n)).
     rewrite -> (Nat.add_assoc 1 1 n).
     rewrite <- BinInt.ZL0.
     rewrite <- (Nat.add_1_l ((n + 1) / 2)).
     rewrite <- (Nat.mul_1_l 2) at 1.
     rewrite <- (Nat.add_assoc (1 * 2) n 1).
     rewrite -> (Nat.div_add_l 1 2 (n + 1)).
     ** reflexivity.
     ** exact (Nat.neq_succ_0 1).
Qed.

(* ***** *)

Lemma even_or_odd :
  forall m : nat,
  (exists q : nat, m = 2 * q) \/ (exists q : nat, m = S (2 * q)).
Proof.
  intro n.
  induction n as [ | n' [[q H_q] | [q H_q]]].
  - left.
    exists 0.
    rewrite -> (Nat.mul_0_r 2).
    reflexivity.

  - (* left.
    rewrite -> H_q. *)
    (*  exists q0 : nat, S (2 * q) = 2 * q0 we found out that if we choose the left disjunct, we run into an impossibility. *)
    right.
    rewrite -> H_q.
    exists q.
    reflexivity.

  - (* right.
    rewrite -> H_q. *)
    left.
    rewrite -> H_q.
    Search ( 1 + _  = S _).
    exists (S q).
    Search (S _ * _ = _).
    Check (Nat.mul_succ_l 1 q).
    rewrite -> (Nat.mul_succ_l 1 q).
    rewrite -> (Nat.mul_1_l q).
    rewrite -> (Nat.mul_succ_l 1 (S q)).
    rewrite -> (Nat.mul_1_l (S q)).
    Check (plus_Sn_m).
    rewrite <- (plus_Sn_m q q).
    Check (plus_n_Sm).
    rewrite -> (plus_n_Sm (S q) q).
    reflexivity.
Qed.

Definition specification_of_mystery_function_13 (mf : nat -> nat) :=
  (forall q : nat, mf (2 * q) = q)
  /\
  (forall q : nat, mf (S (2 * q)) = q).
(* n / 2  *)

Theorem there_is_at_most_one_mystery_function_13:
  forall f g : nat -> nat,
    specification_of_mystery_function_13 f ->
    specification_of_mystery_function_13 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_mystery_function_13.
  intros [H_f_O H_f_S] [H_g_O H_g_S].
  intro n.
  Check (even_or_odd n).
  destruct (even_or_odd n) as [[q H_q] | [q H_q]].

  - rewrite -> H_q.
    rewrite -> (H_g_O q).
    exact (H_f_O q).

  - rewrite -> H_q.
    rewrite -> (H_g_S q).
    exact (H_f_S q).
Qed.

Definition unit_test_for_mystery_function_13 (mf : nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 0) && (mf 2 =n= 1) && (mf 3 =n= 1)
(* etc. *).

Definition mystery_function_13 (n : nat) : nat :=
  n / 2.

Compute (unit_test_for_mystery_function_13 mystery_function_13).

Theorem there_is_at_least_one_mystery_function_13:
  specification_of_mystery_function_13 mystery_function_13.
Proof.
  unfold specification_of_mystery_function_13, mystery_function_13.
  split.

  - intro q.
    rewrite -> (Nat.mul_comm 2 q).
    rewrite -> (Nat.div_mul q 2).
    * reflexivity.
    * exact (Nat.neq_succ_0 1).

  - intro q.
    rewrite <- (Nat.add_1_l (2 * q)).
    rewrite <- (Nat.mul_comm q 2).
    rewrite -> (Nat.div_add 1 q 2).
    assert (H_tmp := Nat.div_1_l 2).
    rewrite -> H_tmp.
    * exact (Nat.add_0_l q).
    * exact (Nat.lt_1_2).
    * exact (Nat.neq_succ_0 1).
Qed.

Definition specification_of_mystery_function_25 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  (forall q : nat,
      mf (2 * (S q)) = S (mf (S q)))
  /\
  mf 1 = 0
  /\
  (forall q : nat,
      mf (S (2 * (S q))) = S (mf (S q))).

(* log *)
(* ****** *)

Theorem there_is_at_most_one_mystery_function_25:
  forall f g : nat -> nat,
    specification_of_mystery_function_25 f ->
    specification_of_mystery_function_25 g ->
    forall n : nat,
      f n = g n.
Proof.
(*
intros f g.
  unfold specification_of_mystery_function_25.
  intros [H_f_O [H_f_S [H_f_1 H_f_SS]]] [H_g_O [H_g_S [H_g_1 H_g_SS]]].
  intro n.
  induction n using pair_induction.
  - rewrite -> H_g_O.
    exact H_f_O.
  - rewrite -> H_g_1.
    exact H_f_1.
  - destruct (even_or_odd n) as [[q H_q] | [q H_q]].
      * rewrite -> H_q.
      assert (H_tmp := H_f_S q).
      rewrite <- (Nat.add_1_l (2 * q)) at 1.
      rewrite <- (Nat.add_1_l (1 + (2 * q))) at 1.
      rewrite -> (Nat.add_assoc 1 1 (2 * q)).
      rewrite <- BinInt.ZL0.
      rewrite <- (Nat.add_1_l q) in H_tmp.
      rewrite -> (Nat.mul_add_distr_l 2 1 q) in H_tmp.
      rewrite -> (Nat.mul_1_r 2) in H_tmp.
      rewrite -> H_tmp.
      rewrite -> (Nat.add_1_l q).
      clear H_tmp.
      assert (H_tmp := H_g_S q).
      rewrite <- (Nat.add_1_l (2 * q)) at 1.
      rewrite <- (Nat.add_1_l (1 + (2 * q))) at 1.
      rewrite -> (Nat.add_assoc 1 1 (2 * q)).
      rewrite <- BinInt.ZL0.
      rewrite <- (Nat.add_1_l q) in H_tmp.
      rewrite -> (Nat.mul_add_distr_l 2 1 q) in H_tmp.
      rewrite -> (Nat.mul_1_r 2) in H_tmp.
      rewrite -> H_tmp.
      rewrite -> (Nat.add_1_l q).
      Search (log _).
      
  induction n using pair_induction.

  - rewrite -> H_g_O.
    exact (H_f_O).
  - rewrite -> H_g_1.
    exact H_f_1.
  - destruct (even_or_odd n) as [[q H_q] | [q H_q]].
    + rewrite -> H_q.
      assert (H_tmp := H_f_S q).
      rewrite <- (Nat.add_1_l (2 * q)) at 1.
      rewrite <- (Nat.add_1_l (1 + (2 * q))) at 1.
      rewrite -> (Nat.add_assoc 1 1 (2 * q)).
      rewrite <- BinInt.ZL0.
      rewrite <- (Nat.add_1_l q) in H_tmp.
      rewrite -> (Nat.mul_add_distr_l 2 1 q) in H_tmp.
      rewrite -> (Nat.mul_1_r 2) in H_tmp.
      rewrite -> H_tmp.
      rewrite -> (Nat.add_1_l q).
      clear H_tmp.
      assert (H_tmp := H_g_S q).
      rewrite <- (Nat.add_1_l (2 * q)) at 1.
      rewrite <- (Nat.add_1_l (1 + (2 * q))) at 1.
      rewrite -> (Nat.add_assoc 1 1 (2 * q)).
      rewrite <- BinInt.ZL0.
      rewrite <- (Nat.add_1_l q) in H_tmp.
      rewrite -> (Nat.mul_add_distr_l 2 1 q) in H_tmp.
      rewrite -> (Nat.mul_1_r 2) in H_tmp.
      rewrite -> H_tmp.
      rewrite -> (Nat.add_1_l q).
      

      Search ( 
      rewrite -> (H_g_O).
      exact (H_f_O q).

    + rewrite -> H_q.
      rewrite -> (H_g_S q).
      exact (H_f_S q).
    
rewrite -> (H_f_S n).
    rewrite -> (H_g_S n).
    rewrite -> IHn.
    reflexivity.
Qed.
*)
Abort.

Definition specification_of_mystery_function_20 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = S (mf i j)).
(* add  *)
(* ****** *)

Theorem there_is_at_most_one_mystery_function_20:
  forall f g : nat -> nat -> nat,
    specification_of_mystery_function_20 f ->
    specification_of_mystery_function_20 g ->
    forall n m: nat,
      f n m = g n m.
Proof.
  intros f g.
  unfold specification_of_mystery_function_20.
  intros [H_f_O H_f_S] [H_g_O H_g_S].
  intro n.
  induction n as [ | n' IHn'].

  - intro m.
    rewrite -> (H_g_O m).
    exact (H_f_O m).

  - intro m.
    rewrite -> (H_f_S n' m).
    rewrite -> (H_g_S n' m).
    rewrite -> (IHn' m).
    reflexivity.
Qed.

Definition unit_test_for_mystery_function_20 (mf : nat -> nat -> nat) :=
  (mf 0 0 =n= 0) && (mf 1 0 =n= 1) && (mf 0 1 =n= 1) && (mf 1 1 =n= 2)
(* etc. *).

Definition mystery_function_20 (n m : nat) : nat :=
  n + m.

Compute (unit_test_for_mystery_function_20 mystery_function_20).


Theorem there_is_at_least_one_mystery_function_20 :
  specification_of_mystery_function_20 mystery_function_20.
Proof.
  unfold specification_of_mystery_function_20, mystery_function_20.
  split.
  - intro j.
    exact (Nat.add_0_l j).

  - intros i j.
    exact (Nat.add_succ_l i j).
Qed.


Definition specification_of_mystery_function_21 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = mf i (S j)).
(* add *)

Theorem there_is_at_most_one_mystery_function_21:
  forall f g : nat -> nat -> nat,
    specification_of_mystery_function_21 f ->
    specification_of_mystery_function_21 g ->
    forall n m: nat,
      f n m = g n m.
Proof.
  intros f g.
  unfold specification_of_mystery_function_21.
  intros [H_f_O H_f_S] [H_g_O H_g_S].
  intro n.
  induction n as [ | n' IHn'].

  - intro m.
    rewrite -> (H_g_O m).
    exact (H_f_O m).

  - intro m.
    rewrite -> (H_f_S n' m).
    rewrite -> (H_g_S n' m).
    rewrite -> (IHn' (S m)).
    reflexivity.
Qed.


Definition unit_test_for_mystery_function_21 (mf : nat -> nat -> nat) :=
  (mf 0 0 =n= 0) && (mf 1 0 =n= 1) && (mf 0 1 =n= 1) && (mf 1 1 =n= 2)
(* etc. *).

Definition mystery_function_21 (n m : nat) : nat :=
  n + m.

Compute (unit_test_for_mystery_function_21 mystery_function_21).

Theorem there_is_at_least_one_mystery_function_21 :
  specification_of_mystery_function_21 mystery_function_21.
Proof.
  unfold specification_of_mystery_function_21, mystery_function_21.
  split.
  - intro j.
    exact (Nat.add_0_l j).

  - intros i j.
    exact (Nat.add_succ_comm i j).
Qed.


(* ****** *)

Definition specification_of_mystery_function_22 (mf : nat -> nat -> nat) :=
  forall i j : nat,
    mf O j = j
    /\
    mf (S i) j = mf i (S j).
(* add  *)

Theorem there_is_at_most_one_mystery_function_22:
  forall f g : nat -> nat -> nat,
    specification_of_mystery_function_22 f ->
    specification_of_mystery_function_22 g ->
    forall n m: nat,
      f n m = g n m.
Proof.
  intros f g.
  unfold specification_of_mystery_function_22.
  intros H_f H_g.
  intro n.
  induction n as [ | n' IHn'].

  - intro m.
    assert (H_tmp := H_g 0 m).
    destruct H_tmp as [H_g_O _].
    rewrite -> H_g_O.  
    assert (H_tmp := H_f 0 m).
    destruct H_tmp as [H_f_O _].
    exact H_f_O.

  - intro m.
    assert (H_tmp := H_g n' m).
    destruct H_tmp as [_ H_g_S].
    rewrite -> H_g_S.
    rewrite <- (IHn' (S m)).
    assert (H_tmp := H_f n' m).
    destruct H_tmp as [_ H_g_f].
    exact H_g_f.
Qed.

Definition unit_test_for_mystery_function_22 (mf : nat -> nat -> nat) :=
  (mf 0 0 =n= 0) && (mf 1 0 =n= 1) && (mf 0 1 =n= 1) && (mf 1 1 =n= 2)
(* etc. *).

Definition mystery_function_22 (n m : nat) : nat :=
  n + m.

Compute (unit_test_for_mystery_function_22 mystery_function_22).

Theorem there_is_at_least_one_mystery_function_22 :
  specification_of_mystery_function_22 mystery_function_22.
Proof.
  unfold specification_of_mystery_function_22, mystery_function_22.
  split.
  - exact (Nat.add_0_l j).

  - exact (Nat.add_succ_comm i j).
Qed.

(* ********** *)

(* Binary trees of natural numbers: *)

Inductive tree : Type :=
  | Leaf : nat -> tree
  | Node : tree -> tree -> tree.

Definition specification_of_mystery_function_19 (mf : tree -> tree) :=
  (forall n : nat,
     mf (Leaf n) = Leaf n)
  /\
  (forall (n : nat) (t : tree),
     mf (Node (Leaf n) t) = Node (Leaf n) (mf t))
  /\
  (forall t11 t12 t2 : tree,
     mf (Node (Node t11 t12) t2) = mf (Node t11 (Node t12 t2))).

(* You might not manage to prove
   that at most one function satisfies this specification (why?),
   but consider whether the following function does.
   Assuming it does, what does this function do?
   And what is the issue here?
*)

Theorem there_is_at_most_one_mystery_function_19:
  forall f g : tree -> tree,
    specification_of_mystery_function_19 f ->
    specification_of_mystery_function_19 g ->
    forall t: tree,
      f t = g t.
Proof.
  intros f g.
  unfold specification_of_mystery_function_21.
  intros [H_f_O [H_f_S H_f_SS]] [H_g_O [H_g_S H_g_SS]].
  intro t.
  induction t as [ | t' IHt'].

  - rewrite (H_g_O n).
    exact (H_f_O n).

  - (* difficult to proceed *)
Abort. 

Fixpoint mystery_function_19_aux (t a : tree) : tree :=
  match t with
  | Leaf n =>
     Node (Leaf n) a
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19_aux t2 a)
  end.

Fixpoint mystery_function_19 (t : tree) : tree :=
  match t with
  | Leaf n =>
     Leaf n
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19 t2)
  end.

Theorem there_is_at_least_one_mystery_function_19 :
  specification_of_mystery_function_19 mystery_function_19.
Proof.
  unfold specification_of_mystery_function_19, mystery_function_19.
  unfold mystery_function_19_aux.
  split.
  - intro n.
    reflexivity.

  - split.
    * reflexivity.
    * reflexivity.
Qed.

(* ********** *)

(* Extra mystery functions: *)

(* ***** *)

Definition specification_of_mystery_function_05 (mf : nat -> nat) :=
  mf 0 = 1
  /\
  forall i j : nat,
    mf (S (i + j)) = 2 * mf i * mf j.

(* ***** *)

Definition specification_of_mystery_function_06 (mf : nat -> nat) :=
  mf 0 = 2
  /\
  forall i j : nat,
    mf (S (i + j)) = mf i * mf j.

(* ***** *)

Definition specification_of_mystery_function_09 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = xorb (mf i) (mf j).

(* ***** *)

Definition specification_of_mystery_function_10 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = (mf i =b= mf j).

(* ***** *)

Definition specification_of_mystery_function_12 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i : nat,
    mf (S (S i)) = (S (S i)) * mf (S i).

(* ***** *)

Definition specification_of_mystery_function_14 (mf : nat -> bool) :=
  (forall q : nat, mf (2 * q) = true)
  /\
  (forall q : nat, mf (S (2 * q)) = false).

(* ********** *)

(* Simple examples of specifications: *)

(* ***** *)

Definition specification_of_the_factorial_function (fac : nat -> nat) :=
  fac 0 = 1
  /\
  forall n' : nat, fac (S n') = S n' * fac n'.

(* ***** *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib n'' + fib (S n'').

(* ********** *)

(* end of week-05_mystery-functions.v *)




