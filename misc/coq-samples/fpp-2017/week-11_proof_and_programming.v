Definition polymorphic_identity (T : Type) (x : T) : T :=
  x.

Definition polymorphic_uncurry (T1 T2 T3 : Type) (f: T1 -> T2 -> T3) (p: T1 * T2) : T3 :=
  match p with
  | (x1, x2) =>
    f x1 x2
  end.


Definition polymorphic_uncurry' (T1 T2 T3 : Type) (f: T1 -> T2 -> T3) :=
  fun (p: T1 * T2) => 
    match p with
    | (x1, x2) =>
      f x1 x2
    end.


Definition polymorphic_uncurry'' :=
  fun (T1 T2 T3 : Type)
      (f: T1 -> T2 -> T3)
      (p: T1 * T2) => 
    match p with
    | (x1, x2) =>
      f x1 x2
    end.


Proposition uncurry :
  forall (T1 T2 T3 : Prop),
    (T1 -> T2 -> T3) -> 
    (T1 /\ T2) ->
    T3.
Proof.
  intros T1 T2 T3 f p.
  destruct p as [x1 x2].
  exact (f x1 x2).
  Show Proof.
  Qed.


  
Definition polymorphic_curry (T1 T2 T3 : Type) (f: T1 * T2 -> T3) :=
  fun x1 => fun x2 => f (x1, x2).

Definition apply (T1 T2 : Type) (f : T1 -> T2) (x : T1) :=
  f x.


(**********)

Proposition modus_ponens :
  forall (A B : Prop),
    (A -> B) -> A -> B.
Proof.
  intros A B H_A_implies_B H_A.
  apply H_A_implies_B.
  exact H_A.

  Restart.
  intros A B H_A_implies_B H_A.
  exact (H_A_implies_B H_A).
  Show Proof.(*(fun (A B : Prop) (H_A_implies_B : A -> B) (H_A : A) => H_A_implies_B H_A)*)
Qed.


Proposition modus_ponens' :
  forall (A B : Prop),
    (A -> B) -> A -> B.
Proof.
  intros A B f a.
  apply f.
  exact a.
  Show Proof.
  (*
    (fun (A B : Prop) (f : A -> B) (a : A) => f a)
   *)
  Restart.
  intros A B f a.
  apply f in a.
  exact a.
  Show Proof.
  (*
    (fun (A B : Prop) (f : A -> B) (a : A) => let a0 := f a : B in a0)
*)
Qed.


Proposition trivial :
  forall (A : Prop),
    A -> A.
Proof.
  intros A H_A.
  exact H_A.
  Show Proof.
  Restart.
  intros T x.
  exact x.
  Show Proof.
  Proof fun (A : Prop) (a : A) => a.


Proposition foo :
  forall A B C : Prop,
    (A -> B) -> (B -> C) -> A -> C /\ C.
Proof.
  intros A B C f g a.
  split.
    apply g; apply f; apply a.
  apply g; apply f; apply a.
  Show Proof.
  (*
    (fun (A B C : Prop) (f : A -> B) (g : B -> C) (a : A) => conj (g (f a)) (g (f a)))
   *)

  Restart.
  intros A B C f g a.
  assert (x := a).
  apply f in x.
  apply g in x.
  split; exact x.
  Show Proof.
  (*
(fun (A B C : Prop) (f : A -> B) (g : B -> C) (a : A) =>
 let x := a : A in let x0 := f x : B in let x1 := g x0 : C in conj x1 x1)
   *)


Lemma baz :
  forall n : nat,
  exists m : nat,
    m = S n.
Proof.
  intro n.
  exists (S n).
  reflexivity.
Show Proof.
Qed.


Lemma baz' :
  forall n : nat,
  exists m : nat,
    n < m.
Proof.
  intro n.
  exists (S n).
  Show Proof.














           