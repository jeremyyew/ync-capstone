(* week-01_functional-programming-in-Coq.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 15 Aug 2017 *)

(* ********** *)

Check 3.




(* Note: "nat" is the type of natural numbers. *)

Compute 3.

(* Note: natural numbers are self-evaluating. *)

(* ********** *)

Compute (4 + 6).

Check (4 + 6).

(* ********** *)

Check (plus 4 6).

(* Note: infix + is syntactic sugar for plus. *)

(* ********** *)

Check (plus 4).

(* Note: and plus refers to a library function. *)

Compute (plus 4).
Compute (plus 3).
Compute (plus 2).
Compute (plus 1).
Compute (plus 0).

(* Note: functions are written as in OCaml,
   with the keyword "fun" followed by the formal parameter
   (and optionally its type), "=>", and the body. *)

Compute (fun m : nat => S m).

(*
   For comparison,
     fun m : nat => S m
   would be written
     (lambda (m) (1+ n))
   in Scheme.
 *)

Compute ((fun m : nat => S m) 3).

(* ********** *)

Definition three := 3.

Check three.

Compute three.

Definition ten := 4 + 6.

Check ten.

Compute ten.

(* ********** *)

(* The following definitions are all equivalent: *)


Definition succ_v0 := fun m : nat => S m.

Definition succ_v1 := fun m => S m.

Definition succ_v2 (m : nat) :=
  S m.

Definition succ_v3 (m : nat) : nat :=
  S m.

Definition succ_v4 m :=
  S m.

(* Note: the definition of succ_v3 is the recommended one here. *)

(* Note: variables are defined once and for all in a file. *)

(* ********** *)

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Definition test_add (candidate: nat -> nat -> nat) : bool :=
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
  (* etc. *)
  .

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => S (add_v1 i' j)
  end.

Compute (test_add add_v1).

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v2 i' (S j)
  end.

Compute (test_add add_v2).

Definition add_v3 (i j : nat) : nat :=
  let fix visit n :=
    match n with
      | O => j
      | S n' => S (visit n')
    end
  in visit i.

Compute (test_add add_v3).

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

Definition test_append (candidate: list_nat -> list_nat -> list_nat) : bool :=
  (candidate nil_nat nil_nat =ns= nil_nat)
  &&
  (candidate nil_nat (cons_nat 10 nil_nat) =ns= (cons_nat 10 nil_nat))
  &&
  (candidate (cons_nat 1 nil_nat) (cons_nat 10 nil_nat) =ns= (cons_nat 1 (cons_nat 10 nil_nat)))
  (* etc. *)
  .

Fixpoint append_v0 (xs ys : list_nat) : list_nat :=
  match xs with
  | nil_nat =>
    ys
  | cons_nat x xs' =>
    cons_nat x (append_v0 xs' ys)
  end.

Compute (test_append append_v0).

(* ***** *)

Definition test_length (candidate: list_nat -> nat) : bool :=
  (candidate nil_nat =n= 0)
  &&
  (candidate (cons_nat 1 nil_nat) =n= 1)
  &&
  (candidate (cons_nat 2 (cons_nat 1 nil_nat)) =n= 2)
  (* etc. *)
  .

Fixpoint length_v0 (xs : list_nat) : nat :=
  match xs with
  | nil_nat =>
    0
  | cons_nat x xs' =>
    S (length_v0 xs')
  end.

Compute (test_length length_v0).

(* ********** *)

Inductive binary_tree : Type :=
  Leaf : nat -> binary_tree
| Node : binary_tree -> binary_tree -> binary_tree.

Fixpoint beq_binary_tree (t1 t2 : binary_tree) : bool :=
  match t1 with
    Leaf n1 =>
    match t2 with
      Leaf n2 =>
      n1 =n= n2
    | Node t21 t22 =>
      false
    end
  | Node t11 t12 =>
    match t2 with
      Leaf n2 =>
      false
    | Node t21 t22 =>
      (beq_binary_tree t11 t21) && (beq_binary_tree t12 t22)
    end
  end.

Notation "A =bt= B" :=
  (beq_binary_tree A B) (at level 70, right associativity).

(* ***** *)

Definition test_number_of_leaves (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 1) =n= 1)
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =n= 2)
  (* etc. *)
  .

Fixpoint number_of_leaves_v0 (t : binary_tree) : nat :=
  match t with
    Leaf n =>
    1
  | Node t1 t2 =>
    (number_of_leaves_v0 t1) + (number_of_leaves_v0 t2)
  end.

Compute (test_number_of_leaves number_of_leaves_v0).

(* ***** *)

Definition test_swap (candidate: binary_tree -> binary_tree) : bool :=
  (candidate (Leaf 1) =bt= (Leaf 1))
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =bt= (Node (Leaf 2) (Leaf 1)))
  (* etc. *)
  .


Definition test_flatten (candidate: binary_tree -> list_nat) : bool :=
  (candidate (Leaf 1) =ns= (cons_nat 1 nil_nat))
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =ns= (cons_nat 1 (cons_nat 2 nil_nat)))
  (* etc. *)
  .

Fixpoint flatten_v0 (t : binary_tree) : list_nat :=
    match t with
    | Leaf n =>
      cons_nat n nil_nat
    | Node t1 t2 =>
      append_v0 (flatten_v0 t1) (flatten_v0 t2)
    end.

Compute (test_flatten flatten_v0).

(*
Fixpoint flatten_v1 (t : binary_tree) : list_nat :=
    match t with
    | Leaf n =>
      cons_nat n nil_nat
    | Node t1 t2 =>
      flatten_v1_aux t1 (flatten_v1 t2)
    end
with flatten_v1_aux (t : binary_tree) (a : list_nat) : list_nat :=
     append_v0 (flatten_v1 t) a.
 *)

Fixpoint flatten_v2 (t : binary_tree) : list_nat :=
    match t with
    | Leaf n =>
      cons_nat n nil_nat
    | Node t1 t2 =>
      flatten_v2_aux t1 (flatten_v2 t2)
    end
with flatten_v2_aux (t : binary_tree) (a : list_nat) : list_nat :=
       match t with
       | Leaf n =>
         append_v0 (cons_nat n nil_nat) a
       | Node t1 t2 =>
         append_v0 (flatten_v2_aux t1 (flatten_v2 t2)) a
       end.

Compute (test_flatten flatten_v2).


  
(* ********** *)

(* end of week-01_functional-programming-in-Coq.v *)
(* Local Variables: *)
(* End: *)

