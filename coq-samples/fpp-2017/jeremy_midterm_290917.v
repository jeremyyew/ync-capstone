(* week-07_binary-trees.v *)
(* Functional Programming and Proving (YSC3236) 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Mon 25 Sep 2017 *)

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
Lemma unfold_embed_Left_Leaf :
  embed_left_binary_tree_into_binary_tree Left_Leaf = Leaf.
Proof. 
  unfold embed_left_binary_tree_into_binary_tree.
  reflexivity.
Qed.

Lemma unfold_embed_Left_Node :
   forall (lt : left_binary_tree) (n : nat),
     embed_left_binary_tree_into_binary_tree (Left_Node lt n)
     = Node (embed_left_binary_tree_into_binary_tree lt) n Leaf.
Proof. 
  unfold embed_left_binary_tree_into_binary_tree.
reflexivity.
Qed.

Lemma unfold_project_Leaf :
  project_binary_tree_into_left_binary_tree Leaf = Some Left_Leaf.
Proof.
  unfold project_binary_tree_into_left_binary_tree.
reflexivity.
Qed.

Lemma unfold_project_Node_Leaf_Leaf :
  forall (n : nat),
    project_binary_tree_into_left_binary_tree (Node Leaf n Leaf)
    = Some (Left_Node Left_Leaf n).
Proof.


Lemma about_project_Left_balanced_tree :
  forall (t: binary_tree),
    left_balanced t = true ->
    exists (lt: left_binary_tree),
      project_binary_tree_into_left_binary_tree t
      = Some lt.     
Proof.
Admitted.

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

  assert (H_p_lb := about_project_Left_balanced_tree).
Abort.

(* ********** *)

Proposition projectable :
  forall t : binary_tree,
    left_balanced t = true ->
    exists lt : left_binary_tree,
      project_binary_tree_into_left_binary_tree t = Some lt.
Proof.
Abort.

(* ********** *)

(* end of week-07_binary-trees.v *)
