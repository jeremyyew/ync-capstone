
Require Import Arith Bool.

Search ((_+_) = (_+_)).
(*
Nat.add_comm:
        forall n m : nat, 
        n + m = m + n
Nat.add_assoc: forall n m p : nat, n + (m + p) = n + m + p
 *)


Proposition foo :
  forall n1 n2 n3 : nat,
    (n3 + n1) + n2 = n1 + (n2 + n3).

Proof.
  intro x.
  
  Restart.
  
  intro n1.
  intro n2.
  intro n3.
  
  Restart.
  
  intros n1 n2 n3.
  (*Note that in goals the parenthesis on LHS is gone because coq is implicitly left-to-right already.*)

  Check (Nat.add_comm n3 n1).
  rewrite -> (Nat.add_comm n3 n1).

  Check (Nat.add_assoc n1 n3 n2).
  rewrite <- (Nat.add_assoc n1 n3 n2).

  Check (Nat.add_comm n3 n2).
  rewrite -> (Nat.add_comm n3 n2).

  reflexivity.

  Restart.

  intros n1 n2 n3.
  
  Check (Nat.add_comm n2 n3).
  rewrite -> (Nat.add_comm n2 n3).

  Check (Nat.add_assoc n1 n3 n2).
  rewrite -> (Nat.add_assoc n1 n3 n2).

  Check (Nat.add_comm n1 n3).
  rewrite -> (Nat.add_comm n1 n3).

  reflexivity.

  Restart.

  intros n1 n2 n3. 
  Check (Nat.add_comm n1 (n2 + n3)).
  rewrite -> (Nat.add_comm n1 (n2 + n3)).
  
  Check (Nat.add_comm n2 (n3 + n1)).
  rewrite -> (Nat.add_comm (n3 + n1) n2).
 
  Check (Nat.add_assoc n2 n3 n1).
  rewrite -> (Nat.add_assoc n2 n3 n1).

  reflexivity.
Qed.
