(* week-02_formalizing-a-proof-in-coq.v *)
(* FPP 2019 - YSC3236 2019-2020, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 22 Aug 2019 *)
(* was: *)
(* Version of 20 Aug 2019 *)

(* ********** *)

Require Import Arith Bool.

(* ********** *)

Search (_ + 0 = _).

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

Check first_formal_proof.

Proposition first_formal_proof' :
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  intro n.
  rewrite -> (Nat.add_0_l n).
  rewrite -> (Nat.add_0_r n).
  reflexivity.
Qed.

Proposition first_formal_proof'' :
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  intro n.
  rewrite -> (Nat.add_0_r n).
  rewrite -> (Nat.add_0_l n).
  reflexivity.

  Restart.

  intro n.
  rewrite -> (Nat.add_0_l n).
  rewrite -> (Nat.add_0_r n).
  reflexivity.
Qed.

Proposition first_formal_proof''' :
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  intro n.
  Check (Nat.add_comm n 0).
  exact (Nat.add_comm n 0).

  Restart.

  intro n.
  Check (Nat.add_comm 0 n).
  symmetry.
  exact (Nat.add_comm 0 n).
Qed.

(* ********** *)

Search (_ + _ = _ + _).

(*
Nat.add_comm: forall n m : nat, n + m = m + n
Nat.add_assoc: forall n m p : nat, n + (m + p) = n + m + p
*)

Check (Nat.add_comm 2 3).

Proposition second_formal_proof :
(*
  forall x : nat,
    forall y : nat,
      forall y : nat,
        x + (y + z) = y + (x + z).
*)
  forall x y z : nat,
    x + (y + z) = y + (x + z).
Proof.
  intro x.
  intro y.
  intro z.

  Restart.

  intros x y z.
  Check (Nat.add_assoc x y z).
  rewrite -> (Nat.add_assoc x y z).    (* rewrite from left to right *)
  Check (Nat.add_comm x y).
  rewrite -> (Nat.add_comm x y).       (* rewrite from left to right *)
  Check (Nat.add_assoc y x z).
  rewrite <- (Nat.add_assoc y x z).    (* rewrite from right to left *)
  reflexivity.

  Restart.

  intros x y z.
  Check (Nat.add_assoc y x z).
  rewrite -> (Nat.add_assoc y x z).
  Check (Nat.add_comm y x).
  rewrite -> (Nat.add_comm y x).
  Check (Nat.add_assoc x y z).
  exact (Nat.add_assoc x y z).
Qed.

(* ********** *)

Proposition third_formal_proof :
  forall n : nat,
    n + 0 + 0 = 0 + 0 + n.
Proof.
  intro n.
  Check (Nat.add_0_r n).
  rewrite -> (Nat.add_0_r n).
  rewrite -> (Nat.add_0_r n).
(*
  rewrite -> (Nat.add_0_l n).
*)
  Check (Nat.add_0_l n).
  Check (Nat.add_0_l 0).
  rewrite -> (Nat.add_0_l 0).
  rewrite -> (Nat.add_0_l n).
  reflexivity.

  Restart.

  intro n.
  rewrite -> (Nat.add_0_r n).
  rewrite -> (Nat.add_0_r n).
  rewrite -> (Nat.add_0_l 0).
  symmetry.
  exact (Nat.add_0_l n).

  Restart.

  Check first_formal_proof.
  intro n.
  Check (first_formal_proof (n + 0)).
  rewrite -> (first_formal_proof (n + 0)).
  Check (first_formal_proof n).
  rewrite -> (first_formal_proof n).
  Check (Nat.add_assoc 0 0 n).
  exact (Nat.add_assoc 0 0 n).

  Restart.

  intro n.
  Check (Nat.add_0_l 0).
  rewrite -> (Nat.add_0_l 0).
  rewrite -> (Nat.add_0_r n).
  exact (first_formal_proof n).
Qed.

(* ********** *)

(* end of week-02_formalizing-a-proof-in-coq.v *)
