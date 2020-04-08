
Require Import List.

Require Import Arith Bool.

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Definition beq_nat_nat A B :=
  match A, B with
    (a1, b1), (a2, b2) =>
    (a1 =n= a2) && (b1 =n= b2)
  end.
                           
Notation "A =nn= B" :=
  (beq_nat_nat A B) (at level 70, right associativity).

Fixpoint beq_list_list A B :=
  match A, B with
  |nil, nil => true
  |nil, _ :: _ => false
  |_::_, nil => false
  |a::as', b::bs' =>
   (a =nn= b) && (beq_list_list as' bs')
  end.

Notation "A =l= B" :=
  (beq_list_list A B) (at level 70, right associativity).


Definition test_cartesian_product_2 (candidate: list nat -> list nat -> list (nat * nat)) : bool :=
  (candidate (1 :: nil)
             (2 :: nil)
  =l= ((1, 2) :: nil))
  &&
  (candidate (1 :: 2 :: nil)
             (3 :: 4 :: nil)
  =l= ((1, 3) :: (1, 4) :: (2, 3) :: (2, 4) :: nil)).
(*
  &&
  (candidate nil
             [10]
   = nil)
  &&
  (candidate nil
             [20; 10]
   = nil)
  &&

  (candidate [1]
             [10]
   = [(1, 10)])
  &&
  (candidate [2; 1]
             [10]
   = [(2, 10); (1, 10)])
  &&
  (candidate [3; 2; 1]
             [10]
   = [(3, 10); (2, 10); (1, 10)])
  &&

  (candidate [1]
             [20; 10]
   = [(1, 20); (1, 10)])
  &&
  (candidate [2; 1]
             [20; 10]
   = [(2, 20); (2, 10);
      (1, 20); (1, 10)])
  &&
  (candidate [3; 2; 1]
             [20; 10]
   = [(3, 20); (3, 10);
      (2, 20); (2, 10);
      (1, 20); (1, 10)])
  &&
  (candidate [4; 3; 2; 1]
             [20; 10]
   = [(4, 20); (4, 10);
      (3, 20); (3, 10);
      (2, 20); (2, 10);
      (1, 20); (1, 10)])
  &&

  (candidate [1]
             [30; 20; 10]
   = [(1, 30); (1, 20); (1, 10)])
  &&
  (candidate [2; 1]
             [30; 20; 10]
   = [(2, 30); (2, 20); (2, 10);
      (1, 30); (1, 20); (1, 10)])
  &&
  (candidate [3; 2; 1]
             [20; 10]
   = [(3, 20); (3, 10);
      (2, 20); (2, 10);
      (1, 20); (1, 10)])
  &&
  (candidate [4; 3; 2; 1]
             [20; 10]
   = [(4, 20); (4, 10);
      (3, 20); (3, 10);
      (2, 20); (2, 10);
      (1, 20); (1, 10)])

  &&
  (candidate [4; 3; 2; 1]
             [30; 20; 10]
   = [(4, 30); (4, 20); (4, 10);
      (3, 30); (3, 20); (3, 10);
      (2, 30); (2, 20); (2, 10);
      (1, 30); (1, 20); (1, 10)])
  (* etc. *).*)


Fixpoint append (A: Type) (vs :list A) (ws: list A) :=
  match vs with
   | nil => ws  
   | v :: vs' =>
     v :: (append A vs' ws)
  end.


Definition cartesian_product_2 (vs_init : list nat) (ws_init : list nat) : list (nat * nat):=
  let fix traverse_1 vs :=
      match vs with
      | nil =>
        nil
      | v :: vs' =>
        let fix traverse_2 ws :=
            match ws with
            | nil =>
              nil 
            | w :: ws' =>
              (v, w) :: (traverse_2 ws')
            end
        in append (nat * nat) (traverse_2 ws_init) (traverse_1 vs')
    end
  in traverse_1 vs_init.


Compute test_cartesian_product_2 cartesian_product_2.

Fixpoint length (T : Type) (ns : list T) : nat :=
  match ns with
  | nil =>
    0
  | n :: ns' =>
    S (length T ns')
  end.

(***********)
(*lambda-lifted*)

Definition cartesian_product_2' (vs_init : list nat) (ws_init : list nat) : list (nat * nat):=
  let fix traverse_1 vs :=
      match vs with
      | nil =>
        nil
      | v :: vs' =>
        let fix traverse_2 ws v:=
            match ws with
            | nil =>
              nil 
            | w :: ws' =>
              (v, w) :: (traverse_2 ws' v)
            end
        in append (nat * nat) (traverse_2 ws_init v) (traverse_1 vs')
    end
  in traverse_1 vs_init.

Compute test_cartesian_product_2 cartesian_product_2.

Fixpoint traverse_2 (ws : list nat) (v :nat) :=
  match ws with
  | nil =>
    nil 
  | w :: ws' =>
    (v, w) :: (traverse_2 ws' v)
  end.

Fixpoint traverse_1 (vs : list nat) (ws : list nat):=
  match vs with
  | nil =>
    nil
  | v :: vs' =>
    append (nat * nat) (traverse_2 ws v) (traverse_1 vs' ws)
  end.


Definition cartesian_product_2''' (vs_init : list nat) (ws_init : list nat) : list (nat * nat):=
  traverse_1 vs_init ws_init.

Compute test_cartesian_product_2 cartesian_product_2'''.

(*******)

Lemma unfold_cartesian_product_2''':
  forall (vs ws : list nat),
    cartesian_product_2''' vs ws = traverse_1 vs ws.
Proof.
  unfold_tactic cartesian_product_2'''.
Qed.
Lemma unfold_traverse_2_nil:
  forall v : nat, 
  traverse_2 nil v = nil. 
Proof.
  unfold_tactic traverse_2.
Qed.

Lemma unfold_traverse_2_cons:
  forall (v w : nat) (ws' : list nat), 
  traverse_2 (w :: ws') v = (v, w) :: (traverse_2 ws' v).
Proof.
  unfold_tactic traverse_2.
Qed.

Lemma unfold_traverse_1_nil:
  forall ws : list nat, 
  traverse_1 nil ws = nil. 
Proof.
  unfold_tactic traverse_1.
Qed.

Lemma unfold_length_nil:
  forall (T : Type),
    length T nil = 0.
Proof.
  unfold_tactic length.
Qed.

Lemma unfold_length_cons:
  forall (T :Type) (n : T) (ns' : list T),
    length T (n :: ns') = S (length T ns').
Proof.
  unfold_tactic length.
Qed.

Lemma unfold_append_nil:
  forall (T : Type) (ws : list T),
    append T nil ws = ws.
Proof.
  unfold_tactic append.
Qed.

Lemma unfold_append_cons:
  forall (T : Type) (v : T) (vs' ws : list T),
    append T (v :: vs') ws = v :: (append T vs' ws).
Proof.
  unfold_tactic append.
Qed.

Lemma unfold_append_nil':
  forall (T : Type) (ws : list T),
    append T ws nil = ws.
Proof.
  intros T ws.
  induction ws as [ | w ws' IHws].
  rewrite -> unfold_append_nil.
  reflexivity.

  rewrite -> unfold_append_cons.
  rewrite -> IHws.
  reflexivity.
Qed.

Lemma unfold_traverse_1_cons:
  forall (v : nat) (vs' ws : list nat), 
    traverse_1 (v :: vs') ws =
    append (nat * nat) (traverse_2 ws v) (traverse_1 vs' ws).
Proof.
  unfold_tactic traverse_1.
Qed.

Lemma unfold_traverse_1_smth_cons:
  forall (w : nat) (vs ws' : list nat), 
    traverse_1 vs (w :: ws') =
    append (nat * nat) (traverse_1 vs (w :: nil)) (traverse_1 vs ws').
Proof.
  Admitted.

Lemma unfold_traverse_1_cons_nil:
  forall vs : list nat, 
  traverse_1 vs nil = nil. 
Proof.
  intro vs.
  induction vs as [ | v vs'].
  rewrite -> (unfold_traverse_1_nil nil).
  reflexivity.
  rewrite -> (unfold_traverse_1_cons v vs' nil). 
  rewrite -> (unfold_traverse_2_nil v).
  rewrite -> IHvs'.  
  rewrite -> (unfold_append_nil (nat * nat) nil).
  reflexivity.
Qed.

Lemma length_of_trav1_list_nat:
  forall (w : nat) (vs : list nat),
    length (nat * nat) (traverse_1 vs (w :: nil)) =
    length (nat) vs. 
Proof.  
  Admitted.
(*******)

Lemma length_of_trav2_nat_list:
  forall (v : nat) (ws' : list nat),
    length (nat * nat) (traverse_2 ws' v) =
    length (nat) ws'. 
Proof.  
  Admitted.
  (*******)

Proposition length_of_appended_lists:
  forall (T : Type) (vs ws : list T),
  length T (append T vs ws) =
  length T vs + length T ws. 
Proof.
  Admitted.

Proposition cardinality_of_cartesian_product :
  forall (vs : list nat) (m : nat),
    length nat vs = m ->
    forall (ws : list nat) (n :nat),
      length nat ws = n ->
   length (nat * nat) (cartesian_product_2''' vs ws) = m * n.
Proof.
  intros vs.
  induction vs as [ | v vs' IHvs'].

  intros m Hvs ws n Hws.
  unfold cartesian_product_2'''.
  rewrite -> unfold_traverse_1_nil.
  rewrite -> unfold_length_nil.
  rewrite -> unfold_length_nil in Hvs.
  rewrite <- Hvs.
  rewrite -> (Nat.mul_0_l n).
  reflexivity.

  intros m Hvs ws.
  induction ws as [ | w ws' IHws'].  
  intros n Hws.
  unfold cartesian_product_2'''.
  rewrite -> (unfold_traverse_1_cons_nil).
  rewrite -> unfold_length_nil.
  rewrite -> unfold_length_nil in Hws.
  rewrite <- Hws.
  rewrite -> (Nat.mul_0_r).
  reflexivity.

  intros n Hws.
  rewrite -> unfold_length_cons in Hvs.
  rewrite -> unfold_length_cons in Hws.
  rewrite <- Hws.
  rewrite <- Hvs.
  rewrite -> unfold_cartesian_product_2'''.
  rewrite -> (unfold_traverse_1_cons).
  rewrite -> unfold_traverse_2_cons.
  rewrite -> unfold_append_cons.
  rewrite -> unfold_length_cons.
  rewrite -> unfold_traverse_1_smth_cons.
  rewrite ->2 length_of_appended_lists.
  rewrite -> length_of_trav1_list_nat.
  rewrite -> length_of_trav2_nat_list.
 (* rewrite -> IHvs'.*)
Abort.