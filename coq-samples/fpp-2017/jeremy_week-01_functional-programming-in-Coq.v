(* week-01_functional-programming-in-Coq.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 27 Aug 2017 *)
(* was: *)
(* Version of 15 Aug 2017 *)

(* ********** *)

(* Your name and e-mail address: 
Jeremy Yew
Jeremy.yew@u.yale-nus.edu.sg *)

(* ********** *)

(* ********** *)

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

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


Definition test_mul (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 0)
  &&
  (candidate 1 0 =n= 0)
  &&
  (candidate 1 1 =n= 1)
  &&
  (candidate 1 2 =n= 2)
  &&
  (candidate 2 1 =n= 2)
  &&
  (candidate 2 2 =n= 4)
  &&
  (candidate 2 3 =n= 6)
(* etc. *)
.

Fixpoint mul_v1 (i j : nat) : nat :=
  match i with
  | O =>
    O
  | S i' => 
    match j with
    | O =>
      O
    | S j' =>
      i + (mul_v1 i j')
    end
  end.

  
Compute (test_mul mul_v1).


Definition test_power (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 1)
  &&
  (candidate 1 0 =n= 1)
  &&
  (candidate 2 0 =n= 1)
  &&
  (candidate 0 1 =n= 0)
  &&
  (candidate 0 2 =n= 0)
  &&
  (candidate 0 10 =n= 0)
  &&
  (candidate 1 1 =n= 1)
  &&
  (candidate 1 2 =n= 1)
  &&
  (candidate 1 10 =n= 1)
  &&
  (candidate 2 1 =n= 2)
  &&
  (candidate 2 2 =n= 4)
  &&
  (candidate 2 10 =n= 1024)
  (* etc. *)
  .

  Fixpoint power_v1 (x n : nat) : nat :=
    match n with
    | O =>
      1
    | S n' =>
      match x with
      | O =>
        O 
      | S x' =>
        mul_v1 x (power_v1 x n')
      end
    end.

Compute (test_power power_v1).


Definition test_fac (candidate: nat -> nat) : bool :=
  (candidate 0 =n= 1)
  &&
  (candidate 1 =n= 1)
  &&
  (candidate 2 =n= 2)
  &&
  (candidate 3 =n= 6)
  &&
  (candidate 4 =n= 24)
  &&
  (candidate 5 =n= 120)
  &&
  (candidate 6 =n= 720)
  (* etc. *) .

Fixpoint fac_v1 (n : nat) : nat :=
  match n with
  | O =>
    1
  | S n'=>
    n * (fac_v1 n')
  end.

Compute (test_fac fac_v1).

Definition test_fib (candidate: nat -> nat): bool :=
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
  (* etc. *)
.

Fixpoint fib_v1 (n : nat) : nat :=
  match n with
  | O =>
    O
  | S n' =>
    match n' with
    | O =>
      1 
    | S n'' =>
      fib_v1 (n'') + fib_v1 (n')
    end
  end.

Compute (test_fib fib_v1).


Fixpoint fibfib (n : nat) : (nat * nat) :=
  match n with
  | O =>
   (O, S O)
  | S n' =>
    let (fib_n_minus_1, fib_n) := fibfib(n')
    in (fib_n, fib_n_minus_1 + fib_n)
  end.

Fixpoint fib_v2 (n : nat) : nat :=
  let (fib_n, fib_n_plus_1) := fibfib n
  in fib_n.

Compute (test_fib fib_v2).

Definition test_even (candidate: nat -> bool) : bool :=
  (eqb (candidate 0) true)&&
  (eqb (candidate 1) false)&&
  (eqb (candidate 2) true)&&
  (eqb (candidate 3) false)&&
  (eqb (candidate 4) true)&&
  (eqb (candidate 5) false)&&
  (eqb (candidate 1000) true)&&
  (eqb (candidate 1001) false)
  (* etc. *)
  .
Fixpoint even_v1 (n : nat) : bool :=
    match n with
    | O =>
      true
    | S n' =>
      negb (even_v1 n')
    end.

  Compute (test_even even_v1).
  
Definition test_odd (candidate: nat -> bool) : bool :=
  (eqb (candidate 0) false)&&
  (eqb (candidate 1) true)&&
  (eqb (candidate 2) false)&&
  (eqb (candidate 3) true)&&
  (eqb (candidate 4) false)&&
  (eqb (candidate 5) true)&&
  (eqb (candidate 1000) false)&&
  (eqb (candidate 1001) true)
  (* etc. *)
  .

Fixpoint odd_v1 (n : nat) : bool :=
  match n with
    | O =>
      false
    | S n' =>
      negb (odd_v1 n')
    end.

Compute (test_odd odd_v1).

(* ***** *)

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

(* ***** *)


Definition test_reverse (candidate : list_nat -> list_nat) : bool :=
 (candidate nil_nat =ns= nil_nat) &&
  (candidate (cons_nat 0 nil_nat) =ns= (cons_nat 0 nil_nat)) &&
  (candidate (cons_nat 0 (cons_nat 1 nil_nat)) =ns= (cons_nat 1 (cons_nat 0 nil_nat))) &&
  (candidate (cons_nat 0 (cons_nat 1 (cons_nat 2 nil_nat))) =ns= (cons_nat 2 (cons_nat 1 (cons_nat 0 nil_nat))))
  (* etc. *)
.

Fixpoint reverse_v0 (xs : list_nat) : list_nat :=
   match xs with
  | nil_nat =>
    nil_nat
  | cons_nat x xs' =>
    append_v0 (reverse_v0 xs') (cons_nat x nil_nat)
  end. 

Compute (test_reverse reverse_v0).

(* ***** *)

Inductive list_nat_nat : Type :=
  nil_nat_nat : list_nat_nat
| cons_nat_nat : nat -> nat -> list_nat_nat -> list_nat_nat.

Fixpoint beq_list_nat_nat (xs ys : list_nat_nat) : bool :=
  match xs with
  | nil_nat_nat =>
    match ys with
    | nil_nat_nat =>
      true
    | cons_nat_nat y1 y2 ys' =>
      false
     end 
  | cons_nat_nat x1 x2 xs' =>
    match ys with
    | nil_nat_nat =>
      false
    | cons_nat_nat y1 y2 ys' =>
      (x1 =n= y1) && (x2 =n= y2) && beq_list_nat_nat xs' ys'
    end
  end. 

Notation "A =nns= B" :=
  (beq_list_nat_nat A B) (at level 70, right associativity).

(* ***** *)

Inductive option_list_nat_nat :=
| None_list_nat_nat : option_list_nat_nat
| Some_list_nat_nat : list_nat_nat -> option_list_nat_nat.

Definition beq_option_list_nat_nat (o1 o2 : option_list_nat_nat) : bool :=
  match o1 with
  | None_list_nat_nat =>
    match o2 with
    | None_list_nat_nat =>
      true
    | Some_list_nat_nat nn2s =>
      false
    end
  | Some_list_nat_nat nn1s =>
    match o2 with
    | None_list_nat_nat =>
      false
    | Some_list_nat_nat nn2s =>
      beq_list_nat_nat nn1s nn2s
    end
   end. 
      
Notation "A =onns= B" :=
  (beq_option_list_nat_nat A B) (at level 70, right associativity).



Definition test_append_nat_nat (candidate: list_nat_nat -> list_nat_nat -> list_nat_nat) : bool :=
  (candidate nil_nat_nat nil_nat_nat =nns= nil_nat_nat)
  &&
  (candidate nil_nat_nat (cons_nat_nat 10 20 nil_nat_nat) =nns= (cons_nat_nat 10 20 nil_nat_nat))
  &&
  (candidate (cons_nat_nat 10 20 nil_nat_nat) (cons_nat_nat 30 40 nil_nat_nat) =nns= (cons_nat_nat 10 20 (cons_nat_nat 30 40 nil_nat_nat)))
  (* etc. *)
  .

Fixpoint append_nat_nat_v0 (xs ys : list_nat_nat) : list_nat_nat :=
  match xs with
  | nil_nat_nat =>
    ys 
  | cons_nat_nat x1 x2 xs' =>
    cons_nat_nat x1 x2 (append_nat_nat_v0 xs' ys)
  end.

  Compute (test_append_nat_nat append_nat_nat_v0).

  
Definition test_scalar_product (candidate : list_nat -> list_nat -> option_list_nat_nat) : bool :=
  ((candidate (cons_nat 1 nil_nat)
              (cons_nat 10 (cons_nat 20 nil_nat)))
   =onns=
   None_list_nat_nat)
  &&
  ((candidate (cons_nat 1 (cons_nat 2 nil_nat))
              (cons_nat 10 nil_nat))
   =onns=
   None_list_nat_nat)
  &&
  ((candidate (cons_nat 1 (cons_nat 2 nil_nat))
              (cons_nat 10 (cons_nat 20 nil_nat)))
   =onns=
   (Some_list_nat_nat (cons_nat_nat 1 10 (cons_nat_nat 2 20 nil_nat_nat))))
  (* etc. *)
.

(* This returns a reversed scalar product.*)
(*
Fixpoint scalar_product_v0 (xs_init ys_init : list_nat) : option_list_nat_nat :=
  let fix visit xs ys a:=
      match xs with
      | nil_nat =>
        match ys with
        | nil_nat =>
          Some_list_nat_nat a
        | cons_nat y ys' =>
          None_list_nat_nat
        end
      | cons_nat x xs' =>
        match ys with
        | nil_nat =>
          None_list_nat_nat 
        | cons_nat y ys' =>
          visit  xs' ys' (cons_nat_nat x y a)
        end
      end 
  in visit xs_init ys_init nil_nat_nat.
  

  Compute (test_scalar_product scalar_product_v0).

*)

Fixpoint scalar_product_v2 (xs_init ys_init: list_nat) : option_list_nat_nat :=
  let fix visit xs ys a:=
      match xs with
      | nil_nat =>
        match ys with
        | nil_nat =>
          Some_list_nat_nat a
        | cons_nat y ys' =>
          None_list_nat_nat
        end
      | cons_nat x xs' =>
        match ys with
        | nil_nat =>
          None_list_nat_nat 
        | cons_nat y ys' =>
        visit xs' ys' (append_nat_nat_v0 a (cons_nat_nat x y nil_nat_nat))
        end
      end 
  in visit xs_init ys_init nil_nat_nat.
  
Compute test_scalar_product scalar_product_v2.

  
(*Without accumulator: assumes xs ys are same length OR returns nil_nat when xs and ys are of different length, instead of option type*)
Fixpoint scalar_product_v1 (xs ys: list_nat) : list_nat_nat :=
  match xs with
  | nil_nat =>
    nil_nat_nat
  | cons_nat x xs' =>
    match ys with
    | nil_nat =>
      nil_nat_nat
    | cons_nat y ys' =>
      cons_nat_nat x y (scalar_product_v1 xs' ys')
    end
  end. 

Definition test_convolve (candidate : list_nat -> list_nat -> option_list_nat_nat) : bool :=
  ((candidate (cons_nat 1 nil_nat)
              (cons_nat 10 (cons_nat 20 nil_nat)))
   =onns=
   None_list_nat_nat)
  &&
  ((candidate (cons_nat 1 (cons_nat 2 nil_nat))
              (cons_nat 10 nil_nat))
   =onns=
   None_list_nat_nat)
  &&
  ((candidate (cons_nat 1 (cons_nat 2 nil_nat))
              (cons_nat 10 (cons_nat 20 nil_nat)))
   =onns=
   (Some_list_nat_nat (cons_nat_nat 1 20 (cons_nat_nat 2 10 nil_nat_nat))))
  (* etc. *)
  .

  (*Attempted there-and-back-again. Didn't work.*)

(*  
Fixpoint convolve_taba (xs ys : list_nat) : list_nat_nat :=
  let fix walk xs k :=
      match xs with
      | nil_nat =>
        k ys nil_nat_nat
      | cons_nat x xs' =>
        let back_again ys r:=
        match ys with
        | nil_nat =>
          nil_nat
        | cons_nat y ys' => 
          k ys' (cons_nat_nat x y r)
        end
        in walk xs' back_again
      end
  in walk xs (fun (n :list_nat) (m : list_nat_nat) => m). 
*)
 (* Compute (test_convolve convolve_taba).*)

Fixpoint convolve_v0 (xs ys : list_nat) : option_list_nat_nat :=
    scalar_product_v2 xs (reverse_v0 ys).

  Compute (test_convolve convolve_v0).


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


Definition test_number_of_nodes (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 1) =n= 0)
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =n= 1)&&
  (candidate (Node (Leaf 3) ((Node (Leaf 1) (Leaf 2)))) =n= 2)
  (* etc. *)
  .  

Fixpoint number_of_nodes_v0 (t : binary_tree) : nat :=
  match t with
    Leaf n =>
    0
  | Node t1 t2 =>
    1 + (number_of_nodes_v0 t1) + (number_of_nodes_v0 t2)
   end.
  

Compute (test_number_of_nodes number_of_nodes_v0).


(* ***** *)


Definition test_smallest_leaf (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 0) =n= 0)&&
  (candidate (Leaf 1) =n= 1)&&
  (candidate (Node (Leaf 1) (Leaf 2)) =n= 1)&&
  (candidate (Node (Leaf 3) ((Node (Leaf 1) (Leaf 2)))) =n= 1)&&
  (candidate (Node (Node (Leaf 3) ((Node (Leaf 1) (Leaf 2)))) (Leaf 0)) =n= 0)                             
  (* etc. *)
  .
  
Fixpoint smallest_leaf_v0 (t : binary_tree) : nat :=
      match t with
      | Leaf n => 
        n
      | Node t1 t2 =>
        min (smallest_leaf_v0 t1) (smallest_leaf_v0 t2)
      end.

Compute (test_smallest_leaf smallest_leaf_v0).


(* ***** *)

Definition test_weight (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 0)
   =n= 0)
  &&
  (candidate (Node (Leaf 1) (Leaf 10))
   =n= 11)
  &&
  (candidate (Node (Leaf 1) (Node (Leaf 10) (Leaf 100)))
   =n= 111)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 10)) (Leaf 100))
   =n= 111)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 10)) (Node (Leaf 100) (Leaf 1000)))
   =n= 1111)
  (* etc. *)
  .

Fixpoint weight_v0 (t : binary_tree) : nat :=
  match t with
  | Leaf n => 
    n
  | Node t1 t2 =>
    weight_v0 t1 + weight_v0 t2
  end.

Compute (test_weight weight_v0).

(* ***** *)


Definition test_height (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 1)
   =n= 0)
  &&
  (candidate (Node (Leaf 1) (Leaf 10))
   =n= 1)
  &&
  (candidate (Node (Leaf 1) (Node (Leaf 10) (Leaf 100)))
   =n= 2)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 10)) (Leaf 100))
   =n= 2)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 10)) (Node (Leaf 100) (Leaf 1000)))
   =n= 2)&&
  (candidate (Node (Node (Node (Leaf 1) (Leaf 2)) (Leaf 10)) (Node (Leaf 100) (Leaf 1000)))
   =n= 3)
  (* etc. *)
  .

Fixpoint height_v0 (t : binary_tree) : nat :=
  match t with
  | Leaf n => 
    0
  | Node t1 t2 =>
    S (max (height_v0 t1) (height_v0 t2))
  end.

Compute (test_height height_v0).

(* ***** *)
Definition test_width (candidate: binary_tree -> nat) : bool :=
   (candidate (Leaf 1)
   =n= 1)
  &&
  (candidate (Node (Leaf 1) (Leaf 10))
   =n= 2)
  &&
  (candidate (Node (Leaf 1) (Node (Leaf 10) (Leaf 100)))
   =n= 2)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 10)) (Leaf 100))
   =n= 2)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 10)) (Node (Leaf 100) (Leaf 1000)))
   =n= 4)&&
  (candidate (Node (Node (Node (Leaf 1) (Leaf 2)) (Leaf 10)) (Node (Leaf 100) (Leaf 1000)))
   =n= 4)
  (* etc. *)
  .
Fixpoint get_width_v0 (t : binary_tree) (n : nat) : nat :=
  match n with
  | O => (*if n = 0*)
    O
  | S n' =>
    match n' with
    | O => (*if n = 1*)
      match t with 
      | Leaf n =>
        S O 
      | Node t1 t2 =>
        S O
      end  (*return 1 no matter what, since the width at level 1 is always 1*)
    | S n'' => (*if n > 1*)
      match t with
      | Leaf n => (*no more trees to traverse, i.e. there are no trees that add to the width at level n*)
        O
      | Node t1 t2 =>
        (get_width_v0 t1 n') + (get_width_v0 t2 n')
      end
    end
  end.
                                 
 
Fixpoint width_v0 (t : binary_tree) : nat :=
  let l := S (height_v0 t) (*height + 1 = number of levels*)
  in let fix visit l:=
         match l with
         | O =>
           O
         | S l' =>
           match l' with
           | O => (*if h = 1*)
             S O (*then width = 1*)
           | S l'' => (*if h > 1*)
            max (get_width_v0 t l) (visit l')
           end
         end
     in visit l. 


Compute (test_width width_v0).


(* ***** *)

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

(* ***** *)

Definition test_swap (candidate: binary_tree -> binary_tree) : bool :=
  (candidate (Leaf 1) =bt= (Leaf 1))
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =bt= (Node (Leaf 2) (Leaf 1)))
  (* etc. *)
  .

Fixpoint swap_v0 (t : binary_tree) : binary_tree :=
  match t with
  | Leaf n =>
    Leaf n
  | Node t1 t2 =>
    Node (swap_v0 t2) (swap_v0 t1)
  end. 

Compute (test_swap swap_v0).

(* ********** *)

(* end of week-01_functional-programming-in-Coq.v *)
