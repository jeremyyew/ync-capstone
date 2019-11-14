(* jeremy_week-07_threeconsec.v *)
(* Functional Programming and Proving (YSC3236) 2017-2018, Sem1 *)


(* ********** *)

(*
   name: Jeremy Yew
   student ID number: A0156262H
   e-mail address: jeremy.yew@u.yale-nus.edu.sg
*)

(* ********** *)

(* Paraphernalia: *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

(* ********** *)

Check (plus_Sn_m).
(*plus_Sn_m
     : forall n m : nat, S n + m = S (n + m)
*)

Lemma SSSn_is_3_plus_n :
  forall n : nat,
  S (S (S n)) = 3 + n.
Proof.
  intro n.
  rewrite <- (Nat.add_1_l n).
  rewrite <- (plus_Sn_m 1 n).
  rewrite <- (plus_Sn_m 2 n).
  reflexivity.
Qed.

Proposition product_of_three_consec :
  forall n : nat,
    exists k : nat,
      n * S (n) * S (S n) = 3 * k.
Proof.
  intro n. 
  induction n as [ | n' IHn'].
  
  Search (0 * _ = 0).
  rewrite -> (Nat.mul_0_l 1).
  rewrite -> (Nat.mul_0_l 2).
  exists 0.
  rewrite -> (Nat.mul_0_r 3).
  reflexivity.

  rewrite -> (SSSn_is_3_plus_n n').
  Check  (Nat.mul_add_distr_r).
  rewrite -> (Nat.mul_add_distr_l (S n' * S (S n')) 3 n').
  rewrite -> (Nat.mul_comm (S n' * S (S n')) n').
  rewrite -> (Nat.mul_assoc n' (S n') (S (S n'))).
  destruct IHn' as [x IHn'].
  rewrite -> IHn'.
  rewrite -> (Nat.mul_comm (S n' * S (S n')) 3).
  Check (Nat.mul_add_distr_l).
  rewrite <- (Nat.mul_add_distr_l 3 (S n' * S (S n')) x).
  exists (S n' * S (S n') + x).
  reflexivity.
Qed.
  