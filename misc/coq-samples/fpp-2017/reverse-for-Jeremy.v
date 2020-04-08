(* reverse-for-Jeremy.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Tue 05 Dec 2017 *)

(* ********** *)

(* oral exam of Jeremy Yew Ern *)

(* ********** *)

(* Standard paraphernalia: *)

Ltac unfold_tactic name :=
  intros;
  unfold name; (* fold name; *)
  reflexivity.
  
Require Import Arith Bool List.

(* ********** *)

(* Unfold lemmas for the infix operator to concatenate lists: *)

Lemma unfold_list_append_nil :
  forall (T : Type)
         (ys : list T),
    nil ++ ys = ys.
Proof.
  unfold_tactic List.app.
Qed.

Lemma unfold_list_append_cons :
  forall (T : Type)
         (x : T)
         (xs' ys : list T),
    (x :: xs') ++ ys =
    x :: (xs' ++ ys).
Proof.
  unfold_tactic List.app.
Qed.

(* ********** *)

(* Task 1:
   implement a polymorphic function that reverses a list
   using list concatenation.
 *)


Fixpoint reverse_v1 (T : Type) (xs : list T) : list T :=
  match xs with
  | nil =>
    nil 
  | x :: xs' =>
    reverse_v1 T xs' ++ (x :: nil)
  end.

Compute (reverse_v1 nat (1 :: 2 :: 3 :: nil)).

(* Verify that the *response* buffer contains:
     = 3 :: 2 :: 1 :: nil
     : list nat
*)

Lemma unfold_reverse_v1_nil :
  forall (T : Type),
  reverse_v1 T (nil) = nil.
Proof.
  unfold_tactic reverse_v1.
Qed.


Lemma unfold_reverse_v1_cons :
  forall (T : Type) (x : T) (xs' : list T),
  reverse_v1 T (x :: xs') = reverse_v1 T xs' ++ (x :: nil).
Proof.
  unfold_tactic reverse_v1.
Qed.
(* ********** *)

(* Task 2:
   implement a polymorphic function that reverses a list
   not using list concatenation but using an accumulator.
 *)

Fixpoint reverse_v2_aux (T : Type) (xs : list T) (a : list T) : list T :=
  match xs with
  | nil =>
    a
  | x :: xs' =>
    reverse_v2_aux T xs' (x :: a)
  end.
  
Definition reverse_v2 (T : Type) (xs : list T) : list T :=
  reverse_v2_aux T xs nil.
  

Compute (reverse_v2 nat (1 :: 2 :: 3 :: nil)).
(* Verify that the *response* buffer contains:
     = 3 :: 2 :: 1 :: nil
     : list nat
 *)


Lemma unfold_reverse_v2_aux_nil :
  forall (T : Type) (a : list T),
    reverse_v2_aux T nil a = a.  
Proof.
  unfold_tactic reverse_v2_aux.
Qed.  

Lemma unfold_reverse_v2_aux_cons :
  forall (T : Type) (x : T) (xs' : list T) (a : list T),
    reverse_v2_aux T (x :: xs') a =
    reverse_v2_aux T xs' (x :: a).  
Proof.
  unfold_tactic reverse_v2_aux.
Qed.  

(* ********** *)

(* Task 3:
   prove that reverse_v1 is an involution
*)

Lemma reverse_v1_distrib_over_append:
  forall (T : Type) (xs ys : list T), 
  reverse_v1 T (xs ++ ys) = (reverse_v1 T ys) ++ (reverse_v1 T xs).
Proof.
  Admitted.
  
  
Proposition reverse_v1_is_involutory :
  forall (T : Type)
         (xs : list T),
    reverse_v1 T (reverse_v1 T xs) = xs.
Proof.
  intros T xs.
  induction xs as [ | x xs' IHxs'].

  rewrite -> unfold_reverse_v1_nil; reflexivity.

  rewrite -> unfold_reverse_v1_cons.
  rewrite -> reverse_v1_distrib_over_append.
  rewrite -> unfold_reverse_v1_cons.
  rewrite -> IHxs'.
  rewrite -> unfold_reverse_v1_nil.
  rewrite -> unfold_list_append_nil.
  rewrite -> unfold_list_append_cons.
  rewrite -> unfold_list_append_nil.
  reflexivity.
Qed.
  (* ********** *)

(* Task 4:
   prove that reverse_v2 is an involution
*)

  (*
Lemma about_reverse_v2_aux :
  forall (T : Type) (xs a : list T),
    reverse_v2_aux T (reverse_v2_aux T xs a) nil =
    a ++ xs.
Proof.
  intros T xs.
  induction xs as [ | x xs' IHxs'].

  intro a. 
  rewrite -> unfold_reverse_v2_aux_nil.
  rewrite -> List.app_nil_r.
  fold (reverse_v2 T a).
*)
Lemma about_reverse_v2_aux_canonical :
  forall (T : Type) (xs a : list T),
    reverse_v2_aux T xs a =
    (reverse_v2_aux T xs nil) ++ a.
Proof.
  Admitted.

  
  Lemma about_reverse_v2_aux :
  forall (T : Type) (xs a : list T),
    reverse_v2_aux T (reverse_v2_aux T xs a) nil =
    (reverse_v2_aux T a xs).
Proof.
  Admitted.



Proposition reverse_v2_is_involutory :
  forall (T : Type)
         (xs : list T),
    reverse_v2 T (reverse_v2 T xs) = xs.
Proof.
  intros T xs.
  unfold reverse_v2.
  induction xs as [ | x xs' IHxs'].

  rewrite -> unfold_reverse_v2_aux_nil.
  reflexivity.


  rewrite -> unfold_reverse_v2_aux_cons.
  (*
  rewrite -> about_reverse_v2_aux.
  rewrite -> unfold_list_append_cons.
  rewrite -> unfold_list_append_nil.
  reflexivity.
*)

  case xs' as [ |x' xs''].

  rewrite -> unfold_reverse_v2_aux_nil.
  rewrite -> unfold_reverse_v2_aux_cons.
  rewrite -> unfold_reverse_v2_aux_nil.
  reflexivity.

  case xs'' as [ |x'' xs'''].
  
  rewrite -> unfold_reverse_v2_aux_cons.
  rewrite -> unfold_reverse_v2_aux_nil.
  rewrite -> unfold_reverse_v2_aux_cons.
  rewrite -> unfold_reverse_v2_aux_cons.
  rewrite -> unfold_reverse_v2_aux_nil.
  reflexivity.

Abort.
 

(* ********** *)

(* Task 5:
   prove that reverse_v1 is a left inverse of reverse_v2
*)

(*
Proposition reverse_v1_is_a_left_inverse_of_reverse_v2 :
  forall (T : Type)
         (xs : list T),
    reverse_v1 T (reverse_v2 T xs) = xs.
Proof.
*)
  
(* ********** *)

(* Task 6:
   prove that reverse_v2 is a left inverse of reverse_v1
*)

(*
Proposition reverse_v2_is_a_left_inverse_of_reverse_v1 :
  forall (T : Type)
         (xs : list T),
    reverse_v2 T (reverse_v1 T xs) = xs.
Proof.
*)

(* ********** *)

(* Task 7:
   prove that reverse_v1 and reverse_2 are extensionally equal
*)

Proposition reverse_v1_and_reverse_v2_are_extensionally_equal :
  forall (T : Type)
         (xs : list T),
    reverse_v1 T xs = reverse_v2 T xs.
Proof.         
  intros T xs.
  unfold reverse_v2.
  induction xs as [ | x xs' IHxs'].

  rewrite -> unfold_reverse_v1_nil.
  rewrite -> unfold_reverse_v2_aux_nil.
  reflexivity.

  rewrite -> unfold_reverse_v1_cons.
  rewrite -> unfold_reverse_v2_aux_cons.
  rewrite -> about_reverse_v2_aux_canonical.

  rewrite <- IHxs'.
  reflexivity.
Qed.
  (* ********** *)

(* end of reverse-for-Jeremy.v *)
