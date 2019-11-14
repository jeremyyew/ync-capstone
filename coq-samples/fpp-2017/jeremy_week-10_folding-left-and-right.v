(* week-10_folding-left-and-right.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Tue 17 Oct 2017 *)

(* ********** *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith List.

(* ********** *)

Definition specification_of_fold_right (T1 T2 : Type) (fold_right : T2 -> (T1 -> T2 -> T2) -> list T1 -> T2) :=
  (forall (nil_case : T2)
          (cons_case : T1 -> T2 -> T2),
     fold_right nil_case cons_case nil =
     nil_case)
  /\
  (forall (nil_case : T2)

          (cons_case : T1 -> T2 -> T2)
          (v : T1)
          (vs' : list T1),
     fold_right nil_case cons_case (v :: vs') =
     cons_case v (fold_right nil_case cons_case vs')).

Definition specification_of_fold_left (T1 T2 : Type) (fold_left : T2 -> (T1 -> T2 -> T2) -> list T1 -> T2) :=
  (forall (nil_case : T2)
          (cons_case : T1 -> T2 -> T2),
     fold_left nil_case cons_case nil =
     nil_case)
  /\
  (forall (nil_case : T2)
          (cons_case : T1 -> T2 -> T2)
          (v : T1)
          (vs' : list T1),
     fold_left nil_case cons_case (v :: vs') =
     fold_left (cons_case v nil_case) cons_case vs').

(*

 * prove whether each of these specifications is unique

 * propose an implementation of fold_right (resp. of fold_left)
   that satisfies the specification of fold_right (resp. of fold_left).
*)


Fixpoint poly_fold_right (T1 T2 : Type) (nil_case : T2) (cons_case : T1 -> T2 -> T2) (xs : list T1) : T2 :=
  match xs with
  | nil =>
    nil_case
  | (v :: vs') =>
    cons_case v (poly_fold_right T1 T2 nil_case cons_case vs')
  end.

Lemma unfold_poly_fold_right_nil:
  forall (T1 T2 : Type) (nil_case : T2) (cons_case : T1 -> T2 -> T2),
    poly_fold_right T1 T2 nil_case cons_case nil = nil_case.
Proof.
  unfold_tactic poly_fold_right.
Qed.

Lemma unfold_poly_fold_right_cons:
  forall (T1 T2 : Type) (nil_case : T2) (cons_case : T1 -> T2 -> T2) (v: T1) (vs' : list T1),
    poly_fold_right T1 T2 nil_case cons_case (v :: vs') = cons_case v (poly_fold_right T1 T2 nil_case cons_case vs').
Proof.
  unfold_tactic poly_fold_right.
Qed.

Proposition poly_fold_right_satisfies_its_specification :
  forall (T1 T2 : Type),
    specification_of_fold_right T1 T2 (poly_fold_right T1 T2).
Proof.
  intros T1 T2.
  unfold specification_of_fold_right.
  split.

  intros nil_case cons_case.
  rewrite -> (unfold_poly_fold_right_nil T1 T2 nil_case cons_case).
  reflexivity.

  intros nil_case cons_case v vs'.
  rewrite -> (unfold_poly_fold_right_cons T1 T2 nil_case cons_case).
  reflexivity.
Qed.
  
Fixpoint poly_fold_left (T1 T2 : Type) (nil_case : T2) (cons_case : T1 -> T2 -> T2) (xs : list T1) : T2 :=
  match xs with
  | nil =>
    nil_case
  | (v :: vs') =>
     poly_fold_left T1 T2 (cons_case v nil_case) cons_case vs'
  end.


Lemma unfold_poly_fold_left_nil:
  forall (T1 T2 : Type) (nil_case : T2) (cons_case : T1 -> T2 -> T2),
    poly_fold_left T1 T2 nil_case cons_case nil = nil_case.
Proof.
  unfold_tactic poly_fold_left.
Qed.

Lemma unfold_poly_fold_left_cons:
  forall (T1 T2 : Type) (nil_case : T2) (cons_case : T1 -> T2 -> T2) (v: T1) (vs' : list T1),
    poly_fold_left T1 T2 nil_case cons_case (v :: vs') =  poly_fold_left T1 T2 (cons_case v nil_case) cons_case vs'.
Proof.
  unfold_tactic poly_fold_left.
Qed.

Proposition poly_fold_left_satisfies_its_specification :
  forall (T1 T2 : Type),
    specification_of_fold_left T1 T2 (poly_fold_left T1 T2).
Proof.
  intros T1 T2.
  unfold specification_of_fold_left.
  split.

  intros nil_case cons_case.
  rewrite -> (unfold_poly_fold_left_nil T1 T2 nil_case cons_case).
  reflexivity.

  intros nil_case cons_case v vs'.
  rewrite -> (unfold_poly_fold_left_cons T1 T2 nil_case cons_case).
  reflexivity.
Qed.
  
(* ********** *)

(*

 * characterize the result of applying
   
   - poly_fold_right and

   - poly_fold_left

   to nil and cons:
*)

Definition poly_righto (T : Type) (xs : list T) : list T :=
  poly_fold_right T (list T) nil (fun v vs => cons v vs) xs.

Compute (poly_righto nat (1 :: 2 :: 3 :: nil)).

Proposition about_poly_righto :
  forall (T : Type)
         (xs : list T),
  (poly_righto T xs) = xs.
Proof.
  intros T xs.
  unfold poly_righto.

  induction xs as [ | x xs' IHxs].
  rewrite -> (unfold_poly_fold_right_nil T (list T) nil (fun (v : T) (vs : list T) => v :: vs)).
  reflexivity.

  rewrite -> (unfold_poly_fold_right_cons T (list T) nil (fun (v : T) (vs : list T) => v :: vs)).
  rewrite -> IHxs. 
  reflexivity.
Qed.
  
Definition poly_lefty (T : Type) (xs : list T) : list T :=
  poly_fold_left T (list T) nil (fun v vs => cons v vs) xs.

Compute (poly_lefty nat (1 :: 2 :: 3 :: nil)).
Compute (poly_lefty nat (1 :: 2 :: 3 :: 4 :: 5 :: nil)).

(*
Fixpoint poly_reverse_aux (T : Type) (xs : list T) (a : list T) : list T :=
      match xs with
      | nil =>
        a
      | x :: xs' =>
        poly_reverse_aux T xs' (x :: a)
      end.

Definition poly_reverse (T: Type) (xs_init : list T) : list T :=
  poly_reverse_aux T xs_init nil.


(*
Lemma unfold_poly_reverse_aux_nil:
  forall (T : Type) (a : list T),
    poly_reverse_aux T nil a = a.
Proof.
  unfold_tactic poly_reverse_aux.
Qed.

Lemma unfold_poly_reverse_aux_cons:
  forall (T : Type) (x : T) (xs' : list T) (a : list T),
    poly_reverse_aux T (x :: xs') a = poly_reverse_aux T xs' (x :: a).
Proof.
  unfold_tactic poly_reverse_aux.
Qed.

Lemma about_poly_reverse_aux:
  forall (T : Type) (nil_case : list T)(xs' : list T) (a : list T),
    poly_fold_left T (list T) nil_case (fun (v : T) (vs : list T) => v :: vs) xs'
    =  (poly_fold_left T (list T) nil (fun (v : T) (vs : list T) => v :: vs) xs') :: nil_case.
  Admitted.*)


*)
Fixpoint append (A: Type) (vs :list A) (ws: list A) :=
  match vs with
   | nil => ws  
   | v :: vs' =>
     v :: (append A vs' ws)
  end.

Lemma unfold_append_nil:
  forall (A : Type) (ws : list A),
    append A nil ws = ws.
Proof.
  unfold_tactic append.
Qed.

Lemma unfold_append_cons:
  forall (A : Type) (v : A) (vs' ws : list A),
    append A (v :: vs') ws = v :: (append A vs' ws).
Proof.
  unfold_tactic append.
Qed.

Lemma unfold_append_nil':
  forall (A : Type) (ws : list A),
    append A ws nil = ws.
Proof.
  intros A ws.
  induction ws as [ | w ws' IHws].
  rewrite -> unfold_append_nil.
  reflexivity.

  rewrite -> unfold_append_cons.
  rewrite -> IHws.
  reflexivity.
Qed.

Lemma append_assoc:
  forall (T: Type) (xs ys zs : list T),
    append T (append T xs ys) zs =
    append T xs (append T ys zs).
Proof.
  intros T xs ys zs.
  induction xs as [ | x xs' IHxs].
  rewrite ->2 unfold_append_nil.
  reflexivity.

  induction ys as [ | y ys' IHys].
  rewrite -> unfold_append_nil.
  rewrite ->3 unfold_append_cons.
  rewrite -> unfold_append_nil'.
  reflexivity.

  induction zs as [ | z zs' IHzs].
  rewrite ->4 unfold_append_cons.
  rewrite ->2 unfold_append_nil'.
  reflexivity.

  rewrite ->4 unfold_append_cons.
  rewrite -> IHxs.
  rewrite -> unfold_append_cons.
  reflexivity.
Qed.

  Fixpoint poly_reverse_append (T: Type) (xs : list T) : list T :=
  match xs with
  | nil =>
    nil
  | x :: xs' =>
    append T (poly_reverse_append T xs') (x :: nil)
  end.

Compute (poly_reverse_append nat (1 :: 2 :: 3 :: 4 :: 5 :: nil)).


Lemma unfold_poly_reverse_append_nil:
  forall (T : Type),
    poly_reverse_append T nil = nil.
Proof.
  unfold_tactic poly_reverse_append.
Qed.

Lemma unfold_poly_reverse_append_cons:
  forall (T : Type) (x : T) (xs' : list T),
    poly_reverse_append T (x :: xs') = append T (poly_reverse_append T xs') (x :: nil).
Proof.
  unfold_tactic poly_reverse_append.
Qed.


Lemma about_poly_lefty_aux:
  forall (T : Type) (xs nil_case : list T),
   poly_fold_left T (list T) nil_case
    (fun (v : T) (vs : list T) => v :: vs) xs =
  append T (poly_fold_left T (list T) nil (fun (v : T) (vs : list T) => v :: vs) xs) nil_case.
Proof.
  intros T xs.
  induction xs as [ | x xs' IHxs'].

  intro nil_case.
  rewrite -> unfold_poly_fold_left_nil.
  rewrite -> unfold_poly_fold_left_nil.
  rewrite -> unfold_append_nil.
  reflexivity.

  intro nil_case.
  rewrite ->2 unfold_poly_fold_left_cons.

  Check (IHxs' (x :: nil_case)).
  rewrite -> (IHxs' (x :: nil_case)).
  Check (IHxs' (x :: nil)).
  rewrite -> (IHxs' (x :: nil)).
  rewrite -> append_assoc.
  rewrite -> unfold_append_cons.
  rewrite -> unfold_append_nil.
  reflexivity.
  Qed.
Proposition about_poly_lefty :
  forall (T : Type) (xs : list T),
    poly_lefty T xs = poly_reverse_append T xs.
Proof.
  intros T xs.
  unfold poly_lefty.

  induction xs as [ | x xs' IHxs].
  rewrite -> (unfold_poly_fold_left_nil T (list T) nil (fun (v : T) (vs : list T) => v :: vs)).
  rewrite -> unfold_poly_reverse_append_nil.
  reflexivity.

  rewrite -> (unfold_poly_fold_left_cons).
  rewrite -> (about_poly_lefty_aux).
  rewrite -> IHxs.
  rewrite -> (unfold_poly_reverse_append_cons).
  reflexivity.
Qed.
(* ********** *)

Definition reverse_w_poly_fold_right (T : Type) (xs : list T) : list T :=
  poly_fold_right T (list T) nil (fun v vs => append T vs (v :: nil)) xs. 

Compute (reverse_w_poly_fold_right nat (1 :: 2 :: 3 :: 4 :: 5 :: nil)).
Compute (poly_reverse_append nat (1 :: 2 :: 3 :: 4 :: 5 :: nil)).
Compute (poly_lefty nat (1 :: 2 :: 3 :: 4 :: 5 :: nil)).

Definition copy_w_poly_fold_left (T : Type) (xs : list T) : list T :=
  poly_fold_left T (list T) nil (fun v vs => append T vs (v :: nil)) xs. 

Compute (copy_w_poly_fold_left nat (1 :: 2 :: 3 :: 4 :: 5 :: nil)).
Compute (poly_righto nat (1 :: 2 :: 3 :: 4 :: 5 :: nil)).

(*

  * define poly_fold_left in term of poly_fold_right,
    and prove that your definition satisfies the specification of fold_left;
  
  * define poly_fold_right in term of poly_fold_left,
    and prove that your definition satisfies the specification of fold_right;
  
 *)
(*
Fixpoint poly_append (T1 T2 : Type) (vs : T2) (ws : list T1) :=
  match vs with
  |
  |
  end.
 *)

Definition poly_fold_left_alt (T1 T2 : Type) (nil_case : T2) (cons_case : T1 -> T2 -> T2) (xs : list T1) : T2 :=
  poly_fold_right T1 T2 nil_case (fun v vs => append T1 (vs) (cons_case v nil_case)) xs.
 


(* <-- UNCOMMENT THIS COMMENT
Definition poly_lefty_alt (T : Type) (xs : list T) : list T :=
  poly_fold_left_alt T (list T) nil (fun v vs => cons v vs) xs.

Compute (poly_lefty_alt nat (1 :: 2 :: 3 :: nil)).
*)

(* <-- UNCOMMENT THIS COMMENT
Proposition poly_fold_left_alt_satisfies_its_specification :
  forall (T1 T2 : Type),
    specification_of_fold_left T1 T2 (poly_fold_left_alt T1 T2).
Proof.
...
*)

(* ***** *)

(* <-- UNCOMMENT THIS COMMENT
Definition poly_fold_right_alt (T1 T2 : Type) (nil_case : T2) (cons_case : T1 -> T2 -> T2) (xs : list T1) : T2 :=
  poly_fold_left ...
*)

(* <-- UNCOMMENT THIS COMMENT
Definition poly_righto_alt (T : Type) (xs : list T) : list T :=
  poly_fold_right_alt T (list T) nil (fun v vs => cons v vs) xs.

Compute (poly_righto_alt nat (1 :: 2 :: 3 :: nil)).
*)

(* <-- UNCOMMENT THIS COMMENT
Proposition poly_fold_right_alt_satisfies_its_specification :
  forall (T1 T2 : Type),
    specification_of_fold_right T1 T2 (poly_fold_right_alt T1 T2).
Proof.
...
*)

(* ********** *)

(*

  * show that
    if the cons case is a function that is associative and commutative,
    applying poly_fold_left and applying poly_fold_right
    to a nil case, this cons case, and a list
    give the same result.

    Does the converse hold?

*)

(* <-- UNCOMMENT THIS COMMENT
Lemma the_grand_finale_aux :
  forall (T : Type)
         (nil_case : T)
         (cons_case : T -> T -> T),
    (forall x y z : T,
        cons_case x (cons_case y z) = cons_case (cons_case x y) z) ->
    (forall x y : T,
        cons_case x y = cons_case y x) ->
    forall (v : T)
           (vs : list T),
      cons_case v (poly_fold_left T T nil_case cons_case vs) =
      poly_fold_left T T (cons_case v nil_case) cons_case vs.
Proof.
  intros T nil_case cons_case H_assoc H_comm v vs.
  revert nil_case.
  induction vs as [ | v' vs' IHvs']; intro nil_case.
Abort.
(* Prove this master lemma. *)
*)

(* <-- UNCOMMENT THIS COMMENT
Theorem the_grand_finale :
  forall (T : Type)
         (nil_case : T)
         (cons_case : T -> T -> T),
    (forall x y z : T,
        cons_case x (cons_case y z) = cons_case (cons_case x y) z) ->
    (forall x y : T,
        cons_case x y = cons_case y x) ->
    forall xs : list T,
      poly_fold_right T T nil_case cons_case xs =
      poly_fold_left  T T nil_case cons_case xs.
Proof.
Admitted.
(* Prove this theorem. *)
*)

(* <-- UNCOMMENT THIS COMMENT
Proposition example_for_plus :
  forall ns : list nat,
    poly_fold_right nat nat 0 plus ns = poly_fold_left nat nat 0 plus ns.
Proof.
  exact (the_grand_finale nat 0 plus plus_assoc plus_comm).
Qed.
*)

(* ********** *)

(* end of week-10_folding-left-and-right.v *)