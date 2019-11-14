(* week-13_fac.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Fri 10 Nov 2017 *)

(* ********** *)

(* Paraphernalia: *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

Definition specification_of_factorial (fac : nat -> nat) :=
  fac 0 = 1
  /\
  forall n' : nat,
    fac (S n') = (S n') * (fac n').

Theorem there_is_only_one_factorial :
  forall fac1 fac2 : nat -> nat,
    specification_of_factorial fac1 ->
    specification_of_factorial fac2 ->
    forall n : nat,
      fac1 n = fac2 n.
Proof.
  intros fac1 fac2.
  unfold specification_of_factorial.
  intros [S_fac1_0 S_fac1_S] [S_fac2_0 S_fac2_S] n.
  induction n as [ | n' IHn'].

  rewrite -> S_fac1_0.
  rewrite -> S_fac2_0.
  reflexivity.

  rewrite -> S_fac1_S.
  rewrite -> S_fac2_S.
  rewrite -> IHn'.
  reflexivity.
Qed.
 
(* ********** *)

Definition test_fac (candidate: nat -> nat) : bool :=
  (candidate 0 =n= 1)
  && 
  (candidate 1 =n= 1)
  && 
  (candidate 2 =n= 2) 
  && 
  (candidate 3 =n= 6) && 
  (candidate 4 =n= 24) 
  && 
  (candidate 5 =n= 120)
  .

(* ********** *)

(* The factorial function in direct style: *)

Fixpoint fac_ds (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => (S n') * (fac_ds n')
  end.

Compute (test_fac fac_ds).

(* Associated unfold lemmas: *)

Lemma unfold_fac_ds_0 :
  fac_ds 0 = 1.
Proof.
  unfold_tactic fac_ds.
Qed.

Lemma unfold_fac_ds_S :
  forall n' : nat,
    fac_ds (S n') = S n' * fac_ds n'.
Proof.
  unfold_tactic fac_ds.
Qed.

(* Main definition: *)

Definition fac_v1 (n : nat) : nat :=
  fac_ds n.

Compute (test_fac fac_v1).

(* Associated unfold lemma: *)

Lemma unfold_fac_v1 :
  forall n : nat,
    fac_v1 n = fac_ds n.
Proof.
  unfold_tactic fac_v1.
Qed.

(* The main definition satisfies the specification: *)

Theorem fac_v1_satisfies_the_specification_of_factorial :
  specification_of_factorial fac_v1.
Proof.
  unfold specification_of_factorial.
  split.

  rewrite -> unfold_fac_v1.
  rewrite -> unfold_fac_ds_0.
  reflexivity.

  intro n'.
  rewrite -> (unfold_fac_v1 (S n')).
  rewrite -> (unfold_fac_v1  n').
  rewrite -> unfold_fac_ds_S.
  reflexivity.
Qed.  
(* ********** *)

(* The factorial function in continuation-passing style: *)

Fixpoint fac_cps (ans : Type) (n : nat) (k : nat -> ans) : ans :=
  match n with
    | O => k 1
    | S n' => fac_cps ans n' (fun v => k (S n' * v))
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fac_cps_0 :
  forall (ans : Type) (k : nat -> ans),
    fac_cps ans 0 k = k 1.
Proof.
  unfold_tactic fac_cps.
Qed.

Lemma unfold_fac_cps_S :
  forall (ans : Type) (n' : nat) (k : nat -> ans),
    fac_cps ans (S n') k = fac_cps ans n' (fun v => k (S n' * v)).
Proof.
  unfold_tactic fac_cps.
Qed.

(* Lemma about resetting the continuation: *)

Lemma about_fac_cps :
  forall (n : nat) (ans : Type) (k : nat -> ans),
    fac_cps ans n k = k (fac_cps nat n (fun v => v)).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  intros ans k.
  rewrite ->2 unfold_fac_cps_0.
  reflexivity.

  intros ans k.
  rewrite ->2 unfold_fac_cps_S.
  rewrite -> IHn'.
  rewrite -> (IHn' nat (fun v : nat => S n' * v)).
  reflexivity.
Qed.

(* Main definition: *)

Definition fac_v2 (n : nat) : nat :=
  fac_cps nat n (fun v => v).

Compute (test_fac fac_v2).

(* Associated unfold lemma: *)

Lemma unfold_fac_v2 :
  forall n : nat,
    fac_v2 n = fac_cps nat n (fun v => v).
Proof.
  unfold_tactic fac_v2.
Qed.

(* The main definition satisfies the specification: *)

Theorem fac_v2_fits_the_specification_of_factorial :
  specification_of_factorial fac_v2.
Proof.
  unfold specification_of_factorial.
  split.
  rewrite -> unfold_fac_v2.
  rewrite -> unfold_fac_cps_0.
  reflexivity.

  intro n'.
  rewrite ->2 unfold_fac_v2.
  rewrite -> unfold_fac_cps_S.
  rewrite -> about_fac_cps.
reflexivity.
Qed.
(* ********** *)

(* end of week-13_fac.v *)
