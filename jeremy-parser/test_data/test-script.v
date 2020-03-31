Require Import Arith Bool.

(* Comment *)
Require Import Nat.
Proposition add_assoc_nested :
  forall a b: nat,
	a = a.
Proof.
  intro [a].
  Check (Nat.add_comm). Check (Nat.add_comm).
Qed.
