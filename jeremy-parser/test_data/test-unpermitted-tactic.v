
Require Import Arith Bool.

Proposition first_formal_proof :
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  intro n.
  Check (Nat.add_0_r n).
  rewrite -> (Nat.add_0_r n).
  Check (Nat.add_0_l n).
  rewrite -> (Nat.add_0_l n).
  reflexivity.
Qed.

(*
Proposition first_formal_proof_easy:
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  easy.
Qed.

Proposition first_formal_proof_auto:
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  auto.
Qed.

*)

Proposition first_formal_proof_trivial:
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  intro n.
  rewrite -> (Nat.add_0_r n).
  trivial.
Qed.
