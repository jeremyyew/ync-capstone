Require Import Arith Bool.

(* Comment *)
Require Import Nat.
Proposition add_assoc_nested :
  forall a b: nat,
	a = a.
Proof.
  intro.
  reflexivity.
Qed.
