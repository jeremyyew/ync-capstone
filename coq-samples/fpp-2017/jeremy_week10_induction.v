Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.


Definition specification_of_ackermann_peter_function (ack : nat -> nat -> nat):=
  (forall n : nat,
      ack 0 n = S n)
  /\
  (forall m : nat,
      ack (S m) 0 = ack m 1)
  /\
  (forall m n : nat,
      ack (S m) (S n) = ack m (ack (S m) n)).


Definition specification_of_ackermann_peter_function' (ack : nat -> nat -> nat):=
  forall m n : nat,
    (ack 0 n = S n)
    /\
    (ack (S m) 0 = ack m 1)
    /\
    (ack (S m) (S n) = ack m (ack (S m) n)).


Proposition extensionality_of_the_specification_of_the_ackermann_peter_function :
  forall f g : nat -> nat -> nat,
    specification_of_ackermann_peter_function f ->
    specification_of_ackermann_peter_function g ->
    forall m n : nat,
      f m n = g m n.
Proof.
  intros f g.
  unfold specification_of_ackermann_peter_function.
  intros [S_f_0_l [S_f_0_r S_f_SS]] [S_g_0_l [S_g_0_r S_g_SS]].

  intro m.
  induction m as [ | m' IHm'].

  intro n.
  rewrite -> S_f_0_l.
  rewrite -> S_g_0_l.
  reflexivity.

  intro n.
  induction n as [ | n' IHn'].
  rewrite -> S_f_0_r.
  rewrite -> S_g_0_r.
  rewrite -> IHm'.
  reflexivity.
  
  rewrite -> S_f_SS.
  rewrite -> S_g_SS.

  rewrite -> IHn'.
  rewrite -> IHm'.
  reflexivity.
Qed.
  
Proposition equivalence_of_the_two_specifications: 
  forall f : nat -> nat -> nat,
    specification_of_ackermann_peter_function f
    <->
    specification_of_ackermann_peter_function' f.
Proof. 
  intro f.
  unfold specification_of_ackermann_peter_function.
  unfold specification_of_ackermann_peter_function'.

  split.
  intros [S_f_0_l [S_f_0_r S_f_SS]].

  intros n m.
  split.
  rewrite -> S_f_0_l.
  reflexivity.
  split.
  rewrite -> S_f_0_r.
  reflexivity.
  rewrite -> S_f_SS.
  reflexivity.

  intros S_f_all.
  split.
  intro n.
  Check (S_f_all 0 n).
  apply (S_f_all 0 n).

  split.
  intro m.
  apply (S_f_all m 0).

  intros m n.
  apply (S_f_all m n).
Qed.  

Fixpoint primitive_iteration (T : Type) (s : T -> T) (z : T) (i : nat) : T :=
  match i with
  | 0 =>
    z
  | S i' =>
    s (primitive_iteration T s z i')
  end.

Lemma unfold_primitive_iteration_0 :
  forall (T : Type) (s : T -> T) (z : T),
    primitive_iteration T s z 0 = z.
Proof.
  unfold_tactic primitive_iteration.
Qed.

Lemma unfold_primitive_iteration_S :
  forall (T : Type) (s : T -> T) (z : T) (n' : nat),
    primitive_iteration T s z (S n') =
    s (primitive_iteration T s z n').
Proof.
  unfold_tactic primitive_iteration.
Qed.

Definition ack_orig (m : nat) :=
  primitive_iteration
    (nat -> nat)
    (fun f n => primitive_iteration nat f (f 1) n)
    S
    m.

Proposition ack_orig_satisfies_the_specification_of_the_ackermann_peter_function :
  specification_of_ackermann_peter_function ack_orig.
Proof.
  unfold specification_of_ackermann_peter_function.
  unfold ack_orig.
  split.

  intro n.
  unfold primitive_iteration.
  reflexivity.

  split.
  intro m.
  Check (unfold_primitive_iteration_0 (nat -> nat) ).
  


Abort.

Fixpoint ack (m : nat) :=
  match m with
  | O =>
    S
  | S m' =>
    fix ack_local (n : nat) :=
    match n with
    | O =>
      ack m' 1
    | S n' =>
      ack m' (ack_local n')
    end
  end.

Lemma unfold_ack_0 :
  ack 0 = S.
Proof.
  unfold_tactic ack.
Qed.

Lemma unfold_ack_S :
  forall m' : nat,
    ack (S m') =
    fix ack_local (n : nat) :=
    match n with
    | O =>
      ack m' 1
    | S n' =>
      ack m' (ack_local n')
    end.
Proof.
  unfold_tactic ack.
Qed. 
Lemma unfold_ack_S_0 :
  forall m' : nat,
    ack (S m') 0 = ack m' 1.
Proof.
  unfold_tactic ack.
Qed.

Lemma unfold_ack_S_S :
  forall m' n': nat,
    ack (S m') (S n') = ack m' (ack (S m') n').
Proof.
  unfold_tactic ack.
Qed.

Proposition ack_satisfies_the_specification_of_the_ackermann_peter_function:
  specification_of_ackermann_peter_function ack.
Proof.
Abort.

Theorem an_inequality_about_the_ackermann_peter_function:
  forall ack : nat -> nat -> nat,
    specification_of_ackermann_peter_function ack ->
    forall m n : nat,
      n < ack m n.
Proof.
  unfold specification_of_ackermann_peter_function.
  intros ack [S_ack_0_l [S_ack_0_r S_ack_SS]].

  intro m.
  induction m as [ | m' IHm'].
  intro n.
  rewrite -> S_ack_0_l.
  Search (_ < S _).
  apply Nat.lt_succ_diag_r.

  induction n as [ | n' IHn'].
  rewrite -> S_ack_0_r.
  Search (S _ < _).
  (*Nat.lt_succ_l: forall n m : nat, S n < m -> n < m*)
  apply (Nat.lt_succ_l 0 (ack m' 1) (IHm' 1)).

  Check (lt_trans).
  (*Nat.lt_trans
     : forall n m p : nat, n < m -> m < p -> n < p*)