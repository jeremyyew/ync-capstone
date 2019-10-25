(*
Functional Programming and Proving (YSC 3236)
Semester 1, 2019-2020
Professor Olivier Danvy

[...]

Week 2 homework
*)






(* EXERCISE 5 *)
Proposition conjunction_associativity :
  forall A B C : Prop,
    (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  intros A B C.
  intros [[H_A H_B] H_C].
  split.
  - exact H_A.
  - exact (conj H_B H_C).
Qed.

(* EXERCISE 6 *)
Proposition disjunction_commutativity :
  forall A B : Prop,
    A \/ B <-> B \/ A.
Proof.
  intros A B.
  split.
  - intros [H_A | H_B].
    + right.
      exact (H_A).
    + left.
      exact (H_B).
  - intros [H_B | H_A].
    + right.
      exact (H_B).
    + left.
      exact (H_A).
Qed.

(* EXERCISE 7 *)
Proposition disjunction_associativity :
  forall A B C : Prop,
    (A \/ B) \/ C -> A \/ (B \/ C).
Proof.
  intros A B C.
  intros [[H_A | H_B] | H_C].
  - left.
    exact (H_A).
  - right.
    + left.
      exact (H_B).
  - right.
    + right.
      exact (H_C).
Qed.

(* EXERCISE 8.1 *)
Proposition disjunction_distributes_over_conjunction_on_the_left :
  forall A B C : Prop,
    A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
  intros A B C.
  Proof.
    intros [H_A | [H_B H_C]].
    split.
    left.
    exact (H_A).
    left.
    exact (H_A).
    split.
    right.
    exact (H_B).
    right.
    exact (H_C).
Qed.      





(* EXERCISE 8.2 *)
Proposition disjunction_distributes_over_conjunction_on_the_right :
  forall A B C : Prop,
    (B /\ C) \/ A -> (B \/ A) /\ (C \/ A).
  intros A B C.
  Proof.
    intros [[H_B H_C] | H_A].
      split.
      left.
      exact(H_B).
      left.
      exact(H_C).
      split.
      right.
      exact(H_A).
      right.
      exact(H_A).
  Qed.

  
(* EXERCISE 9.1 *)
Proposition conjunction_distributes_over_disjunction_on_the_left :
  forall A B C : Prop,
    A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
  intros A B C.
  split.
  * intros [H_A [H_B | H_C]].
  - left.
    split.
    exact (H_A).
    exact (H_B).
  - right.
    split.
    exact (H_A).
    exact (H_C).
    * intros [[H_A H_B] | [H_A H_C]].
      split.
      exact (H_A).
      left.
      exact (H_B).
      split.
      exact (H_A).
      right.
      exact (H_C).
Qed.

(* EXERCISE 9.2 *)
Proposition conjunction_distributes_over_disjunction_on_the_right :
  forall A B C : Prop,
    (B \/ C) /\ A <-> (B /\ A) \/ (C /\ A).
Proof.
  intros A B C.
  split.
  * intros [[H_B | H_C] H_A].
  - left.
    split.
    exact (H_B).
    exact (H_A).
  - right.
    split.
    exact (H_C).
    exact (H_A).
    * intros [[H_B H_A] | [H_C H_A]].
      split.
      left.
      exact (H_B).
      exact (H_A).
      split.
      right.
      exact (H_C).
      exact (H_A).
Qed.



(* Exercise 12 *)
Proposition contrapositive_of_implication :
  forall A B : Prop,
    (A -> B) -> ~B -> ~A.
  intros A B.
  intros H_A_then_H_B not_H_B.
  intro H_A.
  Proof.
    apply not_H_B.
    apply H_A_then_H_B.
    exact (H_A).
Qed.

(* Exercise 13 *)
Proposition contrapositive_of_contrapositive_of_implication :
  forall A B : Prop,
    (~B -> ~A) -> ~~A -> ~~B.
  intros A B.
  intros not_H_B_then_not_H_A not_not_H_A not_H_B.
  Proof.
    apply not_not_H_A.
    apply not_H_B_then_not_H_A.
    apply not_H_B.
Qed.

(* Exercise 14 *)
Proposition double_negation :
  forall A : Prop,
    A -> ~~A.
  intro A.
  Proof.
    intro H_A.
    intro not_H_A.
    apply not_H_A.
    exact (H_A).
Qed.
