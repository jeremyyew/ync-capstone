
Require Import Arith Bool.

Check Nat.add_0_r.

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
