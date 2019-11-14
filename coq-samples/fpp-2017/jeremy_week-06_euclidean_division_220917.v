
(* ********** *)

(* Paraphernalia: *)

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

Theorem euclidean_division:
  forall d : nat,
    (0 < d) ->
    forall n : nat,
    exists q r: nat,
    (r < d
    /\
    n = (q * d) + r).
Proof.
  intros d H_d.
  intro n.
  induction n as [ | k [q [r [H_r H_k]]]].
  exists 0.
  exists 0.
  split.
      apply H_d.
  
    Search (0 * _ = 0).
    Check (Nat.mul_0_l d).
    rewrite -> (Nat.mul_0_l d).
    reflexivity.

    Check (lt_le_S).
    Check (le_lt_or_eq).
    apply (lt_le_S r d) in H_r.
    apply (le_lt_or_eq (S r) d) in H_r.

    destruct H_r as [IH_r | IH_r].
      Search (S _ < _ -> _ < _).
      exists q.
      exists (S r).
      split.
      apply IH_r.
      Check (H_k).
      rewrite -> H_k.

      Search (S (_ + _) = _ + S _).
      rewrite -> (plus_n_Sm (q * d) r).
      reflexivity.

    exists (S q).
    exists 0.
    split.
      apply H_d.
      rewrite -> H_k.
      rewrite <- IH_r.
      Search (S _ = _ + S _).
      rewrite -> (plus_n_Sm (q * (S r)) r).
      Search (S _ * _ = _ * _ + _).
      rewrite -> (Nat.mul_succ_l (q) (S r)).
      Search (_ + 0 = _).
      rewrite -> (Nat.add_0_r (q * S r + S r)).
      reflexivity.
   Qed.