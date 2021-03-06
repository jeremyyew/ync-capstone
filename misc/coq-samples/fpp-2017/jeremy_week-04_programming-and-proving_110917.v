(* week-04_programming-and-proving.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 05 Sep 2017 *)

(* ********** *)

(* Paraphernalia: *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

Definition test_add (candidate: nat -> nat -> nat) :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 1)
  &&
  (candidate 1 0 =n= 1)
  &&
  (candidate 1 1 =n= 2)
  &&
  (candidate 1 2 =n= 3)
  &&
  (candidate 2 1 =n= 3)
  &&
  (candidate 2 2 =n= 4)
  .

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
  | O => j
  | S i' => S (add_v1 i' j)
  end.

Compute (test_add add_v1).

(* Canonical unfold lemmas for recursive definitions: *)

Lemma unfold_add_v1_0 :
  forall j : nat,
    add_v1 0 j = j.
Proof.
  unfold_tactic add_v1.
Qed.

Lemma unfold_add_v1_S :
  forall i' j : nat,
    add_v1 (S i') j = S (add_v1 i' j).
Proof.
  unfold_tactic add_v1.
Qed.

Proposition add_v1_0_n :
  forall n : nat,
    add_v1 0 n = n.
Proof.
  intro n.
  Check (unfold_add_v1_0).
  apply unfold_add_v1_0.

  Restart.
  apply unfold_add_v1_0.
Qed.
  
Lemma add_v1_n_0 :
  forall n : nat,
    add_v1 n 0 = n.
Proof.
  intro i.
  induction i as [  | i' IH_i']. 

  Check (unfold_add_v1_0 0).
  (* apply (unfold_add_v1_0 0). *)
  rewrite (unfold_add_v1_0 0).
  reflexivity.

  Check (unfold_add_v1_S i' 0).
  rewrite -> (unfold_add_v1_S i' 0).
  Check (IH_i').
  rewrite -> IH_i'.
  reflexivity.
Qed. 
Lemma add_v1_assoc :
  forall x y z : nat,
    add_v1 x (add_v1 y z) =
    add_v1 (add_v1 x y) z.
Proof.
  intro x.
  induction x as [ | x' IHx'].

  intros y z.
  rewrite -> (unfold_add_v1_0 (add_v1 y z)).
  rewrite -> (unfold_add_v1_0 y).
  reflexivity.

  intros y z.
  rewrite -> (unfold_add_v1_S x' (add_v1 y z)).
  rewrite -> (unfold_add_v1_S x' y).
  rewrite -> (unfold_add_v1_S (add_v1 x' y)).
  rewrite -> (IHx' y z).
  reflexivity.
Qed.

(* ***** *)

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
  | O => j
  | S i' => add_v2 i' (S j)
  end.

Compute (test_add add_v2).

(* Canonical unfold lemmas for recursive definitions: *)

Lemma unfold_add_v2_0 :
  forall j : nat,
    add_v2 0 j = j.
Proof.
  unfold_tactic add_v2.
Qed.

Lemma unfold_add_v2_S :
  forall i' j : nat,
    add_v2 (S i') j = add_v2 i' (S j).
Proof.
  unfold_tactic add_v2.
Qed.

(* ***** *)


Proposition equivalence_of_add_v1_and_add_v2 :
  forall i j : nat,
    add_v1 i j = add_v2 i j.
Proof.
Admitted.

Proposition add_v2_0_n :
  forall n : nat,
    add_v2 0 n = n.
Proof.
  intro n.
  Check (equivalence_of_add_v1_and_add_v2).
  rewrite <- (equivalence_of_add_v1_and_add_v2 0 n).
  apply unfold_add_v1_0. 
Qed.
Proposition add_v2_n_0 :
  forall n : nat,
    add_v2 n 0 = n.
Proof.
  intro n.
  Check (equivalence_of_add_v1_and_add_v2).
  rewrite <- (equivalence_of_add_v1_and_add_v2 n 0).
  Check (add_v1_n_0).
  rewrite -> add_v1_n_0.
  reflexivity.
Qed.

Lemma add_v2_assoc :
  forall x y z : nat,
    add_v2 x (add_v2 y z) =
    add_v2 (add_v2 x y) z.
Proof.
Abort.

(* ********** *)  

Definition test_min (candidate : nat -> nat -> nat) : bool :=
  (candidate 0 3 =n= 0)
  &&
  (candidate 3 0 =n= 0)
  &&
  (candidate 2 3 =n= 2)
  &&
  (candidate 3 2 =n= 2)
  &&
  (candidate 3 3 =n= 3)
  .

(* ***** *)

(* Lambda-dropped version of min_v1: *)

Fixpoint visit_min_v1 (m_init n_init m n : nat) : nat :=
  match m with
  | 0 => m_init
  | S m' => match n with
            | 0 => n_init
            | S n' => visit_min_v1 m_init n_init m' n'
            end
  end.

Definition min_v1 (m_init n_init : nat) : nat :=
  visit_min_v1 m_init n_init m_init n_init.

Compute (test_min min_v1).

Fixpoint min_v2 (m n : nat) : nat :=
  match m with
  | 0 => 0
  | S m' => match n with
            | 0 => 0
            | S n' => S (min_v2 m' n')
            end
  end.

Compute (test_min min_v2).

(* ***** *)

(* Canonical unfold lemmas for recursive definitions: *)

Lemma unfold_visit_min_v1_0 :
  forall m_init n_init n : nat,
    visit_min_v1 m_init n_init 0 n = m_init.
Proof.
  unfold_tactic visit_min_v1.
Qed.

Lemma unfold_visit_min_v1_S :
  forall m_init n_init m' n : nat,
    visit_min_v1 m_init n_init (S m') n =
    match n with
    | 0 => n_init
    | S n' => visit_min_v1 m_init n_init m' n'
    end.
Proof.
  unfold_tactic visit_min_v1.
Qed.

Lemma unfold_min_v2_0 :
  forall n : nat,
    min_v2 0 n = 0.
Proof.
  unfold_tactic min_v2.
Qed.

Lemma unfold_min_v2_S :
  forall m' n : nat,
    min_v2 (S m') n =
    match n with
    | 0 => 0
    | S n' => S (min_v2 m' n')
    end.
Proof.
  unfold_tactic min_v2.
Qed.

(* ***** *)

Lemma succ_visit_min_v1 :
  forall m n m' n' : nat,
    visit_min_v1 (S m) (S n) m' n' =
    S (visit_min_v1 m n m' n').
Proof.
  intros m n m'.
  induction m' as [ | m'' IHm''].
  
  intro n'.
  Check (unfold_visit_min_v1_0 (S m) (S n) n').
  rewrite -> (unfold_visit_min_v1_0 (S m) (S n) n').
  Check (unfold_visit_min_v1_0 m n n').
  rewrite -> (unfold_visit_min_v1_0 m n n').
  reflexivity.

  intros [ | n'].
  Check (unfold_visit_min_v1_S (S m) (S n) m'' 0).
  rewrite -> (unfold_visit_min_v1_S (S m) (S n) m'' 0).
  rewrite -> (unfold_visit_min_v1_S m n m'' 0).
  reflexivity.

  Check (unfold_visit_min_v1_S (S m) (S n) m'' (S n')).
  rewrite -> (unfold_visit_min_v1_S (S m) (S n) m'' (S n')).
  Check (IHm'' n').
  rewrite -> (IHm'' n').
  Check (unfold_visit_min_v1_S m n m'' (S n')).
  rewrite -> (unfold_visit_min_v1_S m n m'' (S n')).
  reflexivity.
 Qed.
  
  Proposition equivalence_of_min_v1_and_min_v2 :
  forall m n : nat,
    min_v1 m n = min_v2 m n.
Proof.
  unfold min_v1.
  intro m.
  induction m as [ |m' IHm'].

  intro n.
  Check (unfold_visit_min_v1_0 0 n).
  rewrite -> (unfold_visit_min_v1_0 0 n).
  Check (unfold_min_v2_0).
  rewrite -> (unfold_min_v2_0 n).
  reflexivity.

  intros [ | n'].
  Check (unfold_visit_min_v1_S (S m') 0 m' 0).
  rewrite -> (unfold_visit_min_v1_S (S m') 0 m' 0). 
  Check (unfold_min_v2_S m' 0).
  rewrite -> (unfold_min_v2_S m' 0).
  reflexivity.

  Check (unfold_visit_min_v1_S (S m') (S n') m' (S n')).
  rewrite -> (unfold_visit_min_v1_S (S m') (S n') m' (S n')).
  Check (unfold_min_v2_S m' (S n')).
  rewrite -> (unfold_min_v2_S m' (S n')).
  Check (IHm' n'). 
  rewrite <- (IHm' n').

  Check (succ_visit_min_v1 m' n' m' n').
  apply (succ_visit_min_v1 m' n' m' n').
Qed. 

(* ********** *)

Definition test_evenp (candidate : nat -> bool) : bool :=
  (eqb (candidate 0) true)
  &&
  (eqb (candidate 1) false)
  &&
  (eqb (candidate 7) false)
  &&
  (eqb (candidate 8) true)
  &&
  (eqb (candidate 17) false)
  .

Fixpoint evenp_v1 (n : nat) : bool :=
  match n with
  | 0 => true
  | S n' => match n' with
            | 0 => false
            | S n'' => evenp_v1 n''
            end
  end.

Compute (test_evenp evenp_v1).

(* With an inherited attribute, lambda-lifted: *)

Fixpoint visit_evenp_v2 (n : nat) (a : bool) : bool :=
  match n with
  | 0 => a
  | S n' => visit_evenp_v2 n' (negb a)
  end.

Definition evenp_v2 (n : nat) : bool :=
  visit_evenp_v2 n true.

Compute (test_evenp evenp_v2).

Fixpoint evenp_v3 (n : nat) : bool :=
  match n with
  | 0 => true
  | S n' => negb (evenp_v3 n')
  end.

Compute (test_evenp evenp_v3).

(********************************************************************************)
Lemma unfold_evenp_v1_0 :
  forall n : nat,
    evenp_v1 0 = true.
Proof.
  unfold_tactic evenp_v1.
Qed.

Lemma unfold_evenp_v1_S :
  forall n' : nat,
    evenp_v1 (S n') =
    match n' with
            | 0 => false
            | S n'' => evenp_v1 n''
    end.
Proof.
  unfold_tactic evenp_v1.
Qed.

Lemma unfold_visit_evenp_v2_0 :
  forall (n : nat) (a : bool),
   visit_evenp_v2 0 a = a.
Proof.
  unfold_tactic visit_evenp_v2.
Qed.

Lemma unfold_visit_evenp_v2_S :
  forall (n' : nat) (a : bool),
    visit_evenp_v2 (S n') a = visit_evenp_v2 n' (negb a).
Proof.
  unfold_tactic visit_evenp_v2.
Qed.
(********************************************************************************)

   
Lemma about_visit_evenp_v2:
  forall n'' : nat,
    negb (visit_evenp_v2 (S n'') true) = visit_evenp_v2 n'' (negb (negb true)).
Admitted.  

Lemma about_evenp_v1:
  forall n'' : nat,
    (evenp_v1 n'') = negb (evenp_v1 (S n'')).

  intro n''.
  induction n'' as [ | n'' IHn''].
  rewrite -> (unfold_evenp_v1_0 0).
  Check (unfold_evenp_v1_S 0).
  rewrite -> (unfold_evenp_v1_S 0).
  reflexivity.
Admitted.
   
Proposition equivalence_of_evenp_v1_and_evenp_v2 :
  forall n : nat,
    evenp_v1 n = evenp_v2 n.
Proof.
   unfold evenp_v2.
   intros [ | n'].
   Check (unfold_evenp_v1_0 0).
   rewrite -> (unfold_evenp_v1_0 0).
   Check (unfold_visit_evenp_v2_0 0).
   rewrite -> (unfold_visit_evenp_v2_0 0).
   reflexivity.
   
   induction n' as [ | n'' IHn''].
   Check (unfold_evenp_v1_S 0).
   rewrite -> (unfold_evenp_v1_S 0).
   Check (unfold_visit_evenp_v2_S 0).
   rewrite -> (unfold_visit_evenp_v2_S 0).
   Check (unfold_visit_evenp_v2_0 0).
   rewrite -> (unfold_visit_evenp_v2_0 0).
   reflexivity.
   
   Check (unfold_evenp_v1_S).
   rewrite -> (unfold_evenp_v1_S (S n'')).
   Check (unfold_visit_evenp_v2_S (S n'')).   
   rewrite -> (unfold_visit_evenp_v2_S (S n'')).
   Check (unfold_visit_evenp_v2_S n'').

   
   rewrite -> (unfold_visit_evenp_v2_S n'').
     
   (*Check about_visit_evenp_v2.*)
   rewrite <- (about_visit_evenp_v2 n'').

   Check (about_evenp_v1 n'').
   rewrite -> (about_evenp_v1 n'').

   Check (IHn'').
   rewrite -> IHn''.
   reflexivity.
Qed. 
   
Proposition equivalence_of_evenp_v2_and_evenp_v3 :
  forall n : nat,
    evenp_v2 n = evenp_v3 n.
Proof.
Abort.

Proposition equivalence_of_evenp_v1_and_evenp_v3 :
  forall n : nat,
    evenp_v1 n = evenp_v3 n.
Proof.
Abort.

(* ********** *)

Definition test_fac (candidate: nat -> nat) : bool :=
  (candidate 0 =n= 1)
  && 
  (candidate 1 =n= 1)
  && 
  (candidate 2 =n= 2) 
  && 
  (candidate 3 =n= 6) && 
  (candidate 4 =n= 24) 
  && 
  (candidate 5 =n= 120)
  .

Fixpoint fac_v1 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' =>  n * (fac_v1 n')
  end.

Compute (test_fac fac_v1).

Fixpoint visit_fac_v2 (n a : nat) : nat :=
  match n with
  | 0 => a
  | S n' => (visit_fac_v2 n' (n * a))
  end.

Definition fac_v2 (n : nat) : nat :=
  visit_fac_v2 n 1.

Compute (test_fac fac_v2).

Proposition equivalence_of_fac_v1_and_fac_v2 :
  forall n : nat,
    fac_v1 n = fac_v2 n.
Proof.
Abort.

(* ********** *)

Definition test_fib (candidate: nat -> nat) : bool :=
  (candidate 0 =n= 0)
  && 
  (candidate 1 =n= 1)
  && 
  (candidate 2 =n= 1)
  && 
  (candidate 3 =n= 2)
  && 
  (candidate 4 =n= 3)
  && 
  (candidate 5 =n= 5)
  && 
  (candidate 6 =n= 8)
  && 
  (candidate 7 =n= 13)
  && 
  (candidate 8 =n= 21)
  .

Fixpoint fib_v1 (n : nat) : nat :=
  match n with
  | 0 => O
  | S n' => match n' with
            | O => 1
            | S n'' => (fib_v1 n') + (fib_v1 n'')
            end
  end.

Compute (test_fib fib_v1).

Fixpoint visit_fib_v2 (n a1 a2 : nat) : nat :=
  match n with
  | 0 => a1
  | S n' => (visit_fib_v2 n' a2 (a1 + a2))
  end.

Definition fib_v2 (n : nat) : nat :=
  visit_fib_v2 n 0 1.

Compute (test_fib fib_v2).

Fixpoint visit_fib_v3 (n : nat) : nat * nat :=
  match n with
  | 0 => (0, 1)
  | S n' => match visit_fib_v3 n' with
              | (a1, a2) => (a2, a1 + a2)
            end
  end.

Definition fib_v3 (n : nat) : nat :=
  match visit_fib_v3 n with
    | (a1, a2) => a1
  end.

Compute (test_fib fib_v3).

Proposition equivalence_of_fib_v1_and_fib_v2 :
  forall n : nat,
    fib_v1 n = fib_v2 n.
Proof.
Abort.

Proposition equivalence_of_fib_v1_and_fib_v3 :
  forall n : nat,
    fib_v1 n = fib_v3 n.
Proof.
Abort.

(* ********** *)

Inductive list_nat : Type :=
  nil_nat : list_nat
| cons_nat : nat -> list_nat -> list_nat.

Fixpoint beq_list_nat (xs ys : list_nat) : bool :=
  match xs with
    nil_nat =>
    match ys with
      nil_nat =>
      true
    | cons_nat y ys' =>
      false
    end
  | cons_nat x xs' =>
    match ys with
      nil_nat =>
      false
    | cons_nat y ys' =>
      (x =n= y) && beq_list_nat xs' ys'
    end
  end.

Notation "A =ns= B" :=
  (beq_list_nat A B) (at level 70, right associativity).

(* ***** *)

Definition test_append_list_nat (candidate: list_nat -> list_nat -> list_nat) :=
  (candidate nil_nat nil_nat =ns= nil_nat)
  &&
  (candidate nil_nat (cons_nat 10 nil_nat) =ns= (cons_nat 10 nil_nat))
  &&
  (candidate (cons_nat 1 nil_nat) (cons_nat 10 nil_nat) =ns= (cons_nat 1 (cons_nat 10 nil_nat)))
  (* etc. *)
  .

Fixpoint append_list_nat (xs ys : list_nat) : list_nat :=
  match xs with
  | nil_nat =>
    ys
  | cons_nat x xs' =>
    cons_nat x (append_list_nat xs' ys)
  end.

Compute (test_append_list_nat append_list_nat).

(* Canonical unfold lemmas for recursive definitions: *)

Lemma unfold_append_list_nat_nil_nat :
  forall ys : list_nat,
    append_list_nat nil_nat ys = ys.
Proof.
  unfold_tactic append_list_nat.
Qed.

Lemma unfold_append_list_nat_cons_nat :
  forall (x : nat) (xs' ys : list_nat),
    append_list_nat (cons_nat x xs') ys =
    cons_nat x (append_list_nat xs' ys).
Proof.
  unfold_tactic append_list_nat.
Qed.

Lemma append_nil_nat_ys :
  forall ys : list_nat,
    append_list_nat nil_nat ys = ys.
Proof.
Abort.

Lemma append_ys_nil_nat :
  forall xs : list_nat,
    append_list_nat xs nil_nat = xs.
Proof.
Abort.

Lemma append_list_nat_assoc :
  forall xs ys zs : list_nat,
    append_list_nat xs (append_list_nat ys zs) =
    append_list_nat (append_list_nat xs ys) zs.
Proof.
Abort.

(* ***** *)

Definition test_length_list_nat (candidate: list_nat -> nat) :=
  (candidate nil_nat =n= 0)
  &&
  (candidate (cons_nat 1 nil_nat) =n= 1)
  &&
  (candidate (cons_nat 2 (cons_nat 1 nil_nat)) =n= 2)
  (* etc. *)
  .

Fixpoint length_list_nat_v1 (xs : list_nat) : nat :=
  match xs with
  | nil_nat =>
    0
  | cons_nat x xs' =>
    S (length_list_nat_v1 xs')
  end.

Compute (test_length_list_nat length_list_nat_v1).

Fixpoint visit_length_list_nat_v2 (xs : list_nat) (a : nat) : nat :=
  match xs with
  | nil_nat =>
    a
  | cons_nat x xs' =>
    visit_length_list_nat_v2 xs' (S a)
  end.

Definition length_list_nat_v2 (xs : list_nat) : nat :=
  visit_length_list_nat_v2 xs 0.

Compute (test_length_list_nat length_list_nat_v2).

Proposition equivalence_of_length_list_nat_v1_and_length_list_nat_v2 :
  forall xs : list_nat,
    length_list_nat_v1 xs = length_list_nat_v2 xs.
Proof.
Abort.

(* ********** *)

Proposition append_and_length_commute_with_each_other :
  forall xs ys : list_nat,
    length_list_nat_v1 (append_list_nat xs ys) =
    (length_list_nat_v1 xs) + (length_list_nat_v1 ys).
Proof.
Abort.

(* ********** *)

Inductive binary_tree : Type :=
  Leaf : nat -> binary_tree
| Node : binary_tree -> binary_tree -> binary_tree.

Definition test_number_of_leaves (candidate: binary_tree -> nat) :=
  (candidate (Leaf 1) =n= 1)
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =n= 2)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)) =n= 3)
  (* etc. *)
  .

Fixpoint number_of_leaves_v1 (t : binary_tree) : nat :=
  match t with
    Leaf n =>
    1
  | Node t1 t2 =>
    (number_of_leaves_v1 t1) + (number_of_leaves_v1 t2)
  end.

Compute (test_number_of_leaves number_of_leaves_v1).

Fixpoint visit_number_of_leaves_v2 (t : binary_tree) (a : nat) : nat :=
  match t with
    Leaf n =>
    S a
  | Node t1 t2 =>
    visit_number_of_leaves_v2 t1 (visit_number_of_leaves_v2 t2 a)
  end.

Definition number_of_leaves_v2 (t : binary_tree) : nat :=
  visit_number_of_leaves_v2 t 0.

Compute (test_number_of_leaves number_of_leaves_v1).

Proposition equivalence_of_number_of_leaves_v1_and_number_of_leaves_v2 :
  forall t : binary_tree,
    number_of_leaves_v1 t = number_of_leaves_v2 t.
Proof.
Abort.

(* ********** *)

(* end of week-04_programming-and-proving.v *)
