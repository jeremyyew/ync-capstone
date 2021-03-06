(* week-06_miscellany.v *)
(* FPP 2019 - YSC3236 2019-2020, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 17 Sep 2019 *)

(* ********** *)

Require Import Arith Bool.

(* ********** *)

Lemma truism :
  forall P : nat -> Prop,
    (exists n : nat,
        P n) ->
    exists n : nat,
      P n.
Proof.
  intros P H_P.
  destruct H_P as [n H_Pn].
  exists n.
  exact H_Pn.

  Restart.

  intros P [n H_Pn].
  exists n.
  exact H_Pn.
Qed.

(* ********** *)

Lemma about_the_existential_quantifier_and_disjunction :
  forall P Q : nat -> Prop,
    (exists n : nat, P n \/ Q n)
    <->
    ((exists n : nat, P n)
     \/
     (exists n : nat, Q n)).
Proof.
Abort.

(* ********** *)

Lemma about_the_universal_quantifier_and_conjunction :
  forall P Q : nat -> Prop,
    (forall n : nat, P n /\ Q n)
    <->
    ((forall n : nat, P n)
     /\
     (forall n : nat, Q n)).
Proof.
Abort.

(* ********** *)

Lemma even_or_odd_v1 :
  forall n : nat,
    (exists q : nat,
        n = 2 * q)
    \/
    (exists q : nat,
        n = S (2 * q)).
Proof.
Abort.

Lemma even_or_odd_v2 :
  forall n : nat,
    exists q : nat,
      n = 2 * q
      \/
      n = S (2 * q).
Proof.
Abort.

(* ********** *)

Lemma O_or_S :
  forall n : nat,
    n = 0 \/ (exists n' : nat, 
                 n = S n').
Proof.
  intro n.
  destruct n as [ | n'] eqn:H_n.

  - left.
    reflexivity.

  - right.
    exists n'.
    reflexivity.
Qed.

(* ********** *)

Proposition now_what :
  (forall n : nat, n = S n) <-> 0 = 1.
Proof.
  split.

  - intro H_n_Sn.
    Check (H_n_Sn 0).
    exact (H_n_Sn 0).
    
  - intro H_absurd.
    discriminate H_absurd.
Qed.

Proposition what_now :
  forall n : nat,
    n = S n <-> 0 = 1.
Proof.
  intro n.
  split.

  - intro H_n.
    Search (_ <> S _).
    Check (n_Sn n).
    assert (H_tmp := n_Sn n).
    unfold not in H_tmp.
    Check (H_tmp H_n).
    contradiction (H_tmp H_n).

  - intro H_absurd.
    discriminate H_absurd.
Qed.

(* ********** *)

(* end of week-06_miscellany.v *)
