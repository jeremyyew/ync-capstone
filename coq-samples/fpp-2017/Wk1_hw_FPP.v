(* week-01_functional-programming-in-Coq.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Jeremy Yew  <jeremy.yew@u.yale-nus.edu.sg> *)
(* Version of 19 Aug 2017 *)
(* ********** *)

(*
Ex1. 
Revisit all the standard functions over natural numbers and program them in Coq, including unit tests: addition, multiplication, exponentiation, factorial function, Fibonacci function, and evenness / oddness function using single (instead of mutual) recursion.*)


Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Definition test_mult (candidate: nat -> nat -> nat) : bool :=
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

Fixpoint mult_v0 (i j : nat) : nat :=
  match i with
  | O =>
    O
  | S i' => 
    match j with
    | O =>
      O
    | S j' =>
      i + (mult_v0 i j')
    end
  end.



Compute (test_mult mult_v0).


Definition mult_v1 (i_init j_init: nat) : nat :=
  let fix visit i j :=
      match i with
      | O =>
        O
      | S i' =>
        match j with
        | O =>
          O
        | S j' =>
          i + (visit i j')
        end
      end
   in visit i_init j_init.

Compute (test_mult mult_v1).

Definition test_exp (candidate: nat -> nat -> nat) : bool :=
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
Notation "A * B" :=
  (mult A B)(at level 40, left associativity): nat_scope.


Definition exp_v0 (x_init y_init: nat) : nat :=
  let fix visit x y :=
      match y with
      | O =>
        1
      | S y' =>
        match x with
        | O =>
          O 
        | S x' =>
          x * (visit x y')
        end
      end
  in visit x_init y_init.

Compute (test_exp exp_v0).

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

Definition fac_v0 (x_init : nat) : nat :=
   let fix visit x :=
       match x with
       | O =>
         1
       | S x'=>
         x * (visit x')
       end
   in visit x_init.

Compute (test_fac fac_v0).

Definition fac_v1 (x_init : nat) : nat :=
   let fix visit x a :=
       match x with
       | O =>
         a
       | S x'=>
         visit x' (a * x) 
       end
   in visit x_init 1.

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

Fixpoint fib_v0 (n : nat) : nat :=
  match n with
  | O =>
    O
  | S n' =>
    match n' with
    | O =>
      1 
    | S n'' =>
      fib_v0 (n'') + fib_v0 (n')
    end
  end.

Compute (test_fib fib_v0).


(*Coq supports both tuples and let...in declarations.*)

Fixpoint fibfib (n : nat) : (nat * nat) :=
  match n with
  | O =>
   (O, S O)
  | S n' =>
    let (fib_n_minus_1, fib_n) := fibfib(n')
    in (fib_n, fib_n_minus_1 + fib_n)
  end.

Fixpoint fib_v1 (n : nat) : nat :=
  let (fib_n, fib_n_plus_1) := fibfib n
  in fib_n.

Compute (test_fib fib_v1).

Notation "A == B" :=
  (eqb A B) (at level 100).

Definition test_even (candidate: nat -> bool) : bool :=
  (candidate 0 == true) &&
  (candidate 1 == false) &&
  (candidate 2 == true) &&
  (candidate 3 == false) &&
  (candidate 4 == true) &&
  (candidate 5 == false) &&
  (candidate 1000 == true) &&
  (candidate 1001 == false)
  (* etc. *)
  .

Notation "! A" :=
  (negb A) (at level 100).
  
  Fixpoint even_v0 (n : nat) : bool :=
    match n with
    | O =>
      true
    | S n' =>
      ! (even_v0 n')
    end.

Compute (test_even even_v0).
  
Definition test_odd (candidate: nat -> bool) : bool :=
  (candidate 0 == false) &&
  (candidate 1 == true) &&
  (candidate 2 == false) &&
  (candidate 3 == true) &&
  (candidate 4 == false) &&
  (candidate 5 == true) &&
  (candidate 1000 == false) &&
  (candidate 1001 == true)
  (* etc. *)
  .
  
  Fixpoint odd_v0 (n : nat) : bool :=
    match n with
    | O =>
      false
    | S n' =>
      ! (odd_v0 n')
    end.

  Compute (test_odd odd_v0).

(*
Ex2. 
Implement a function that reverses a list of natural numbers; a function that computes the scalar product of two lists of natural numbers; and a function that computes the convolution of two lists of natural numbers. If needed, use the following option type:*)


Inductive list_nat :=
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

Fixpoint append_v0 (xs ys : list_nat) : list_nat :=
  match xs with
  | nil_nat =>
    ys
  | cons_nat x xs' =>
    cons_nat x (append_v0 xs' ys)
  end.

Definition test_reverse (candidate: list_nat -> list_nat): bool :=
  (candidate nil_nat =ns= nil_nat) &&
  (candidate (cons_nat 0 nil_nat) =ns= (cons_nat 0 nil_nat)) &&
  (candidate (cons_nat 0 (cons_nat 1 nil_nat)) =ns= (cons_nat 1 (cons_nat 0 nil_nat))) &&
  (candidate (cons_nat 0 (cons_nat 1 (cons_nat 2 nil_nat))) =ns= (cons_nat 2 (cons_nat 1 (cons_nat 0 nil_nat))))
  (* etc. *)
.

Fixpoint reverse_v0 (vs: list_nat): list_nat :=
  match vs with
  | nil_nat =>
    nil_nat
  | cons_nat v vs' =>
    append_v0 (reverse_v0 vs') (cons_nat v nil_nat)
  end. 

Compute (test_reverse reverse_v0).

Definition test_atoi (candidate: nat -> list_nat): bool:=
  (candidate 0 =ns= nil_nat) &&
  (candidate 1 =ns= (cons_nat 0 nil_nat)) &&
  (candidate 2 =ns= (cons_nat 1 (cons_nat 0 nil_nat))) &&
  (candidate 3 =ns= (cons_nat 2 (cons_nat 1 (cons_nat 0 nil_nat)))) &&
  (candidate 4 =ns= (cons_nat 3 (cons_nat 2 (cons_nat 1 (cons_nat 0 nil_nat)))))
  (* etc. *)
  .

Definition atoi (n_init: nat): list_nat:=
  let fix build n:=
      match n with
      | O =>
        nil_nat
      | S n' =>
        (cons_nat n' (build n'))
      end
  in build n_init.
      
Compute (test_atoi atoi).

Definition atoi_generic (f: nat -> nat) (n_init: nat ): list_nat :=
  let fix build n :=
      match n with
      | O =>
       nil_nat
      | S n' =>
       (cons_nat (f (n')) (build n'))
      end
  in build n_init.


Compute (test_atoi (atoi_generic (fun n => n))).

Definition atoi_constant (n_init: nat): list_nat :=
  let fix build n :=
      match n with
      | O =>
       nil_nat
      | S n' =>
       (cons_nat (n_init -1) (build n'))
      end
  in build n_init.

Compute atoi_constant 5.

(*For v0, either list being empty means the list of products is empty, even if the lengths do not match.*)

Definition test_dot_prod_v0 (candidate: list_nat -> list_nat -> list_nat): bool:=
  (candidate nil_nat nil_nat =ns= nil_nat)&&
  (candidate nil_nat (atoi 1) =ns= nil_nat)&&                                          
  (candidate (atoi 1) nil_nat =ns= nil_nat)&&
  (candidate (atoi 1) (atoi 1) =ns= atoi_constant 1) &&                                       
  (candidate (atoi 2) (reverse_v0 (atoi 2)) =ns= (atoi_constant 2)) &&                          (candidate (atoi 5) (reverse_v0 (atoi 5)) =ns= (atoi_constant 5)) &&
  (candidate (atoi 10) (reverse_v0 (atoi 10)) =ns= (atoi_constant 10))
  .                     

  Definition dot_prod_v0 (xs_init ys_init: list_nat): list_nat :=
    let fix visit xs ys:=
        match xs with
        | nil_nat =>
          nil_nat
        | cons_nat x xs' =>
          match ys with
          | nil_nat =>
            nil_nat
          | cons_nat y ys' =>
            cons_nat (x * y) (visit xs' ys')
          end 
        end 
    in visit xs_init ys_init.
        
  Compute (test_dot_prod_v0 dot_prod_v0).

  (*This time, we use a test with option types for when lengths do not match.
Note we must define both option_list_nat and beq_option_list_nat. 
Also, in dot_prod_v1, the list_nat is stored in the accumulator. The return type is only determined at the base case, since option_list_nat is not recursive(?). 

Is there a way to implement without accumulator? 
*)

Inductive option_list_nat :=
| None_list_nat : option_list_nat
| Some_list_nat : list_nat -> option_list_nat.

Fixpoint beq_option_list_nat (xso yso : option_list_nat) : bool :=
  match xso with
    None_list_nat =>
    match yso with
      None_list_nat =>
      true
    | Some_list_nat ys =>
      false
    end
  | Some_list_nat xs =>
    match yso with
      None_list_nat =>
      false
    | Some_list_nat ys =>
      (xs =ns= ys)
    end
  end.

Notation "A =nso= B" :=
  (beq_option_list_nat A B) (at level 70, right associativity).


Definition test_dot_prod_v1 (candidate: list_nat -> list_nat -> option_list_nat): bool:=
  (candidate nil_nat nil_nat =nso= (Some_list_nat nil_nat))&&
  (candidate nil_nat (atoi 1) =nso= None_list_nat)&&                                          
  (candidate (atoi 1) (atoi 1) =nso= None_list_nat) &&                                       
  (candidate (atoi 2) (reverse_v0 (atoi 2)) =nso= Some_list_nat (atoi_constant 2)) &&
  (candidate (atoi 5) (reverse_v0 (atoi 5)) =nso= Some_list_nat (atoi_constant 5)) &&
  (candidate (atoi 10) (reverse_v0 (atoi 10)) =nso= Some_list_nat (atoi_constant 10))&&
  (candidate (atoi 9) (reverse_v0 (atoi 10)) =nso= None_list_nat)
.                     

  
  Definition dot_prod_v1 (xs_init ys_init: list_nat): option_list_nat :=
    let fix visit xs ys a:=
        match xs with
        | nil_nat =>
          match ys with
          | nil_nat =>
            Some_list_nat a
          | cons_nat y ys' =>
            None_list_nat
          end
        | cons_nat x xs' =>
          match ys with
          | nil_nat =>
            None_list_nat
          | cons_nat y ys' =>
           visit xs' ys' (cons_nat (x*y) a)
          end 
        end 
    in visit xs_init ys_init nil_nat.
        
  Compute (test_dot_prod_v1 dot_prod_v1).

  (*Convolution: another time*)


  (*Ex 3.
Revisit all the standard functions over binary trees and program them in Coq, including unit tests: number of nodes, smallest leaf (you will need to implement a boolean-valued function comparing two natural numbers), weight, height, width, flatten, well-balancedness of a mobile, and swap. If there is an opportunity to use accumulators, go for it.
 *)

  
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

Definition test_swap (candidate: binary_tree -> binary_tree) : bool :=
  (candidate (Leaf 1) =bt= (Leaf 1))
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =bt= (Node (Leaf 2) (Leaf 1)))
  (* etc. *)
  .

  Fixpoint swap_v0 (t: binary_tree): binary_tree :=
    match t with
    | Leaf n =>
      Leaf n
    | Node t1 t2 =>
      Node (swap_v0 t2) (swap_v0 t1)
    end. 
    
Compute (test_swap swap_v0).



Definition test_smallest_leaf (candidate: binary_tree -> nat): bool :=
  (candidate (Leaf 1) =n= 1)
.


Definition smallest_leaf_v0 (t_init: binary_tree) : nat :=
  let fix visit t a:=
      match t with
    | Leaf n => 
      if n lt a
  return 
    | Node t1 t2 =>
      Node (swap_v0 t2) (swap_v0 t1)
    end.


  
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




                                              
(* Local Variables: *)
(* coq-prog-name: "/usr/local/bin/coqtop" *)
(* coq-load-path: nil *)
(* End: *)

