(* week-07_binary-trees.v *)
(* Functional Programming and Proving (YSC3236) 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Tues 10 Oct 2017 *)

(* ********** *)

(*
   name: Jeremy Yew
   student ID number: A0156262H
   e-mail address: jeremy.yew@u.yale-nus.edu.sg
*)

(* ********** *)

(* Paraphernalia: *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

(* ********** *)

Inductive binary_tree : Type :=
| Leaf : binary_tree
| Node : binary_tree -> nat -> binary_tree -> binary_tree.

Fixpoint left_balanced (t : binary_tree) : bool :=
  match t with
  | Leaf =>
    true
  | Node t1 n t2 =>
    match t2 with
    | Leaf =>
      left_balanced t1
    | Node _ _ _ =>
      false
    end
  end.

Lemma unfold_left_balanced_Leaf :
  left_balanced Leaf = true.
Proof.
  unfold_tactic left_balanced.
Qed.

(* generic unfold lemma: *)

Lemma unfold_left_balanced_Node :
  forall (t1 : binary_tree)
         (n : nat)
         (t2 : binary_tree),
    left_balanced (Node t1 n t2) = match t2 with
                                   | Leaf =>
                                     left_balanced t1
                                   | Node _ _ _ =>
                                     false
                                   end.
Proof.
  unfold_tactic left_balanced.
Qed.

(* specific unfold lemmas: *)

Lemma unfold_left_balanced_Node_Leaf :
  forall (t1 : binary_tree)
         (n : nat),
  left_balanced (Node t1 n Leaf) = left_balanced t1.
Proof.
  unfold_tactic left_balanced.
Qed.

Lemma unfold_left_balanced_Node_Node :
  forall (t1 : binary_tree)
         (n : nat)
         (t1': binary_tree)
         (n' : nat)
         (t2': binary_tree),
  left_balanced (Node t1 n (Node t1' n' t2')) =  false.
Proof.
  unfold_tactic left_balanced.
Qed.

(* ********** *)

Inductive left_binary_tree : Type :=
| Left_Leaf : left_binary_tree
| Left_Node : left_binary_tree -> nat -> left_binary_tree.

Fixpoint embed_left_binary_tree_into_binary_tree (lt : left_binary_tree) : binary_tree :=
  match lt with
  | Left_Leaf =>
    Leaf
  | Left_Node lt n =>
    Node (embed_left_binary_tree_into_binary_tree lt) n Leaf
  end.

Fixpoint project_binary_tree_into_left_binary_tree (t : binary_tree) : option left_binary_tree :=
  match t with
  | Leaf =>
    Some Left_Leaf
  | Node t1 n t2 =>
    match t2 with
    | Leaf =>
      (match project_binary_tree_into_left_binary_tree t1 with
       | Some lt1 =>
         Some (Left_Node lt1 n)
       | None =>
         None
       end)
    | Node _ _ _ =>
      None
    end
  end.

(* ********** *)

Lemma unfold_embed_Left_Leaf :
  embed_left_binary_tree_into_binary_tree Left_Leaf = Leaf.
Proof. 
  unfold_tactic embed_left_binary_tree_into_binary_tree.
Qed.

Lemma unfold_embed_Left_Node :
   forall (lt : left_binary_tree) (n : nat),
     embed_left_binary_tree_into_binary_tree (Left_Node lt n)
     = Node (embed_left_binary_tree_into_binary_tree lt) n Leaf.
Proof. 
  unfold_tactic embed_left_binary_tree_into_binary_tree.
Qed.

Lemma unfold_project_Leaf :
  project_binary_tree_into_left_binary_tree Leaf = Some Left_Leaf.
Proof.
  unfold_tactic project_binary_tree_into_left_binary_tree.
Qed.


(* generic unfold lemma: *)

Lemma unfold_project_Node :
  forall (t1 t2 : binary_tree) (n: nat),
    project_binary_tree_into_left_binary_tree (Node t1 n t2) =
    match t2 with
    | Leaf =>
      (match project_binary_tree_into_left_binary_tree t1 with
       | Some lt1 =>
         Some (Left_Node lt1 n)
       | None =>
         None
       end)
    | Node _ _ _ =>
      None
    end.
Proof.
  unfold_tactic project_binary_tree_into_left_binary_tree.
Qed.

(*specific unfold_lemma*)
Lemma unfold_project_Node_Leaf_Leaf :
  forall (n : nat),
    project_binary_tree_into_left_binary_tree (Node Leaf n Leaf)
    = Some (Left_Node Left_Leaf n).
Proof.
  unfold_tactic project_binary_tree_into_left_binary_tree.
Qed.


Lemma unfold_project_Node_Tree_Leaf :
  forall (t1 : binary_tree) (n: nat),
    project_binary_tree_into_left_binary_tree (Node t1 n Leaf)
    = match project_binary_tree_into_left_binary_tree t1 with
       | Some lt1 =>
         Some (Left_Node lt1 n)
       | None =>
         None
       end.
Proof.
  unfold_tactic project_binary_tree_into_left_binary_tree.
Qed.


(***************)
Proposition projecting_an_embedded_binary_tree :
  forall lt : left_binary_tree,
    project_binary_tree_into_left_binary_tree
      (embed_left_binary_tree_into_binary_tree lt)
    = Some lt.
Proof.
  intro lt.
  induction lt as [ | lt IH_lt].
  rewrite -> unfold_embed_Left_Leaf.
  rewrite -> unfold_project_Leaf.
  reflexivity.

  rewrite -> (unfold_embed_Left_Node lt n).
  rewrite -> (unfold_project_Node_Tree_Leaf).

  rewrite -> IH_lt.
  reflexivity. 
  Qed.


(************)
Lemma about_left_balanced_Node:
  forall (t1 t2 : binary_tree) (n : nat),
  left_balanced (Node t1 n t2) = true -> t2 = Leaf.
Proof.
  intros t1 t2 n.
  case t2 as [  | t1' n' t2' ].
  intro A.
  reflexivity.

  rewrite -> (unfold_left_balanced_Node_Node t1 n t1' n' t2').
  intro A.
  discriminate A.
Qed.

(*For posterity:

Lemma project_t1_with_existential_lt1_initial :
  forall (t1 : binary_tree) (n: nat),
    exists lt1 : left_binary_tree,
      project_binary_tree_into_left_binary_tree t1 = Some lt1
      ->
      project_binary_tree_into_left_binary_tree (Node t1 n Leaf)
      = Some (Left_Node lt1 n).
Proof.
  Abort.

Lemma project_t1_with_existential_lt1 :
  forall (t1 : binary_tree) (n: nat),
    (exists lt1 : left_binary_tree,
      project_binary_tree_into_left_binary_tree t1 = Some lt1)
      ->
      (exists lt : left_binary_tree,
      project_binary_tree_into_left_binary_tree (Node t1 n Leaf)
      = Some lt).
Proof.
  intros t n H.
  destruct H as [lt1 H].
  rewrite -> (unfold_project_Node_Tree_Leaf t n).
  rewrite -> H.
  exists (Left_Node lt1 n).
  reflexivity.
Qed.
*)
  
Proposition projectable :
  forall t : binary_tree,
    left_balanced t = true ->
    exists lt : left_binary_tree,
      project_binary_tree_into_left_binary_tree t = Some lt.
Proof.
  (*For posterity: 

  intros t H_lb.
  induction t.
 
  rewrite -> unfold_project_Leaf.
  exists Left_Leaf.
  reflexivity.

  assert (H_A := about_left_balanced_Node).
  assert (H_t2_Leaf := H_lb).
  apply (H_A t1 t2 n) in H_t2_Leaf.
  rewrite -> (H_t2_Leaf).
  rewrite -> H_t2_Leaf in H_lb.
  rewrite -> unfold_left_balanced_Node_Leaf in H_lb.
  apply IHt1 in H_lb.
  assert (H_e_lt1 := project_t1_with_existential_lt1).
  apply (H_e_lt1 t1 n) in H_lb.
  apply H_lb.
  Restart.
*)
  intro t.
  induction t as [ | t1 IH_t1 n [ | t21 n2 t22] IH_t2].

  rewrite -> unfold_left_balanced_Leaf.
  rewrite -> unfold_project_Leaf.
  intro H_true.
  exists Left_Leaf.
  reflexivity.

  rewrite -> (unfold_left_balanced_Node_Leaf t1 n).
  rewrite -> (unfold_project_Node_Tree_Leaf t1 n).
  intro H_t1.
  Check (IH_t1 H_t1).
  destruct (IH_t1 H_t1) as [lt1 H_lt1].
  rewrite -> H_lt1.
  exists (Left_Node lt1 n).
  reflexivity.

  rewrite -> (unfold_left_balanced_Node_Node t1 n t21 n2 t22).
  intro H_absurd; discriminate H_absurd.
Qed.
(* ********** *)

(* end of week-07_binary-trees.v *)
