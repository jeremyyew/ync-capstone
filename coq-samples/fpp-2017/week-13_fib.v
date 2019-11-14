(* week-13_fib.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Fri 10 Nov 2017 *)

(* ********** *)

(* Paraphernalia: *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Specialized induction principle: *)

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i))) ->
    forall n : nat,
      P n.
Proof.
  intros P H_bc0 H_bc1 H_ic n.
  assert (H_Pn_PSn : P n /\ P (S n)).
    induction n as [ | n' [IH_n' IH_Sn']].
  
    split.

      apply H_bc0.

    apply H_bc1.
  
    split.

      apply IH_Sn'.

    apply (H_ic n' IH_n' IH_Sn').

  destruct H_Pn_PSn as [H_Pn _].
  apply H_Pn.
Qed.

(* ********** *)

Definition specification_of_fibonacci (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib (S n'') + fib n''.

Theorem there_is_only_one_fibonacci :
  forall fib1 fib2 : nat -> nat,
    specification_of_fibonacci fib1 ->
    specification_of_fibonacci fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  unfold specification_of_fibonacci.
  intros [H_fib1_bc0 [H_fib1_bc1 H_fib1_ic]]
         [H_fib2_bc0 [H_fib2_bc1 H_fib2_ic]]
         n.
  induction n as [ | | n'' IHn'' IHSn''] using nat_ind2.

  rewrite -> H_fib2_bc0.
  apply H_fib1_bc0.

  rewrite -> H_fib2_bc1.
  apply H_fib1_bc1.

  rewrite -> H_fib1_ic.
  rewrite -> IHSn''.
  rewrite -> IHn''.
  rewrite <- H_fib2_ic.
  reflexivity.
Qed.

(* ********** *)

(* Standard unit-test function: *)

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

(* ********** *)

(* The fibonacci function in direct style: *)

Fixpoint fib_ds (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => match n' with
                | 0 => 1
                | S n'' => fib_ds n' + fib_ds n''
              end
  end.

Compute (test_fib fib_ds).

(* Associated unfold lemmas: *)

Lemma unfold_fib_ds_0 :
  fib_ds 0 = 0.
Proof.
  unfold_tactic fib_ds.
Qed.

Lemma unfold_fib_ds_1 :
  fib_ds 1 = 1.
Proof.
  unfold_tactic fib_ds.
Qed.

Lemma unfold_fib_ds_SS :
  forall n'' : nat,
    fib_ds (S (S n'')) = fib_ds (S n'') + fib_ds n''.
Proof.
  unfold_tactic fib_ds.
Qed.

(* Main definition: *)

Definition fib_v1 (n : nat) : nat :=
  fib_ds n.

Compute (test_fib fib_v1).

(* Associated unfold lemma: *)

Lemma unfold_fib_v1 :
  forall n : nat,
    fib_v1 n = fib_ds n.
Proof.
  unfold_tactic fib_v1.
Qed.

(* The main definition satisfies the specification: *)

Theorem fib_v1_fits_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v1.
Proof.
  unfold specification_of_fibonacci.
  split.

    rewrite -> unfold_fib_v1.
    apply unfold_fib_ds_0.

  split.

    rewrite -> unfold_fib_v1.
    apply unfold_fib_ds_1.

  intro n''.
  rewrite -> unfold_fib_v1.
  apply unfold_fib_ds_SS.
Qed.

(* ********** *)

(* The fibonacci function in continuation-passing style: *)

Fixpoint fib_cps (ans : Type) (n : nat) (k : nat -> ans) : ans :=
  match n with
    | 0 => k 0
    | S n' =>
      match n' with
        | 0 => k 1
        | S n'' =>
          fib_cps ans n' (fun v1 =>
                            fib_cps ans n'' (fun v2 =>
                                               k (v1 + v2)))
      end
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_cps_0 :
  forall (ans : Type) (k : nat -> ans),
    fib_cps ans 0 k = k 0.
Proof.
  unfold_tactic fib_ds.
Qed.

Lemma unfold_fib_cps_1 :
  forall (ans : Type) (k : nat -> ans),
    fib_cps ans 1 k = k 1.
Proof.
  unfold_tactic fib_ds.
Qed.

Lemma unfold_fib_cps_SS :
  forall (ans : Type) (n'' : nat) (k : nat -> ans),
    fib_cps ans (S (S n'')) k =
    fib_cps ans (S n'') (fun v1 => fib_cps ans n'' (fun v2 => k (v1 + v2))).
Proof.
  unfold_tactic fib_ds.
Qed.

(* Lemma about resetting the continuation: *)

Lemma about_fib_cps :
  forall (n : nat) (ans: Type) (k : nat -> ans),
    fib_cps ans n k = k (fib_cps nat n (fun a => a)).
Proof.
  intro n.
  induction n as [ | | n' IHn' IHn''] using nat_ind2.
  intros ans k.
  rewrite ->2 unfold_fib_cps_0.
  reflexivity.
  
  intros ans k.
  rewrite ->2 unfold_fib_cps_1.
  reflexivity.

  intros ans k.
  rewrite ->2 unfold_fib_cps_SS.
  rewrite -> IHn''.
  rewrite -> IHn'.
  rewrite -> (IHn'' nat (fun v1 : nat => fib_cps nat n' (fun v2 : nat => v1 + v2))).
  rewrite -> (IHn' nat (fun v2 : nat => fib_cps nat (S n') (fun a : nat => a) + v2)).
  reflexivity.
Qed.
      
(* Main definition: *)

Definition fib_v2 (n : nat) : nat :=
  fib_cps nat n (fun v => v).

Compute (test_fib fib_v2).

(* Associated unfold lemma: *)

Lemma unfold_fib_v2 :
  forall n : nat,
    fib_v2 n = fib_cps nat n (fun v => v).
Proof.
  unfold_tactic fib_v2.
Qed.

(* The main definition satisfies the specification: *)

Theorem fib_v2_fits_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v2.
Proof.
Abort.

(* ********** *)

(* The fibonacci function with an accumulator: *)

Fixpoint fib_acc (n a1 a0 : nat) : nat :=
  match n with
    | 0 => a0
    | S n' => fib_acc n' (a1 + a0) a1
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_acc_0 :
  forall a1 a0 : nat,
    fib_acc 0 a1 a0 = a0.
Proof.
  unfold_tactic fib_acc.
Qed.

Lemma unfold_fib_acc_S :
  forall n' a1 a0 : nat,
    fib_acc (S n') a1 a0 = fib_acc n' (a1 + a0) a1.
Proof.
  unfold_tactic fib_acc.
Qed.

(* Main definition: *)

Definition fib_v3 (n : nat) : nat :=
  fib_acc n 1 0.

Compute (test_fib fib_v3).

(* Associated unfold lemma: *)

Lemma unfold_fib_v3 :
  forall n : nat,
    fib_v3 n = fib_acc n 1 0.
Proof.
  unfold_tactic fib_v3.
Qed.

(* Eureka lemma: *)

Lemma about_fib_acc :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall j i : nat,
      fib_acc j (fib (S i)) (fib i) = fib (j + i).
Proof.
Abort.

(* The main definition satisfies the specification: *)

Theorem fib_v3_fits_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v3.
Proof.
Abort.

(* ********** *)

(* The fibonacci function with an accumulator in CPS: *)

Fixpoint fib_acc_cps (ans : Type) (n a1 a0 : nat) (k : nat -> ans) : ans :=
  match n with
    | 0 => k a0
    | S n' => fib_acc_cps ans n' (a1 + a0) a1 k
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_acc_cps_0 :
  forall (ans: Type)
         (a1 a0 : nat)
         (k : nat -> ans),
    fib_acc_cps ans 0 a1 a0 k = k a0.
Proof.
  unfold_tactic fib_acc_cps.
Qed.

Lemma unfold_fib_acc_cps_S :
  forall (ans: Type)
         (n' a1 a0 : nat)
         (k : nat -> ans),
    fib_acc_cps ans (S n') a1 a0 k =
    fib_acc_cps ans n' (a1 + a0) a1 k.
Proof.
  unfold_tactic fib_acc_cps.
Qed.

(* Main definition: *)

Definition fib_v4 (n : nat) : nat :=
  fib_acc_cps nat n 1 0 (fun a => a).

Compute (test_fib fib_v4).

(* Associated unfold lemma: *)

Lemma unfold_fib_v4 :
  forall (n : nat),
    fib_v4 n = fib_acc_cps nat n 1 0 (fun a => a).
Proof.
  unfold_tactic fib_v4.
Qed.

(* Eureka lemma: *)

Lemma about_fib_acc_cps :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall (ans : Type)
           (j i : nat)
           (k : nat -> ans),
      fib_acc_cps ans j (fib (S i)) (fib i) k =
      k (fib (j + i)).
Proof.
Abort.

(* The main definition satisfies the specification: *)

Theorem fib_v4_fits_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v4.
Proof.
Abort.

(* ********** *)

(* The fibonacci function with a co-accumulator: *)

Fixpoint fib_co_acc (n : nat) : nat * nat :=
  match n with
    | O => (1, 0)
    | S n' => let (a1, a0) := fib_co_acc n'
              in (a1 + a0, a1)
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_co_acc_0 :
  fib_co_acc 0 = (1, 0).
Proof.
  unfold_tactic fib_co_acc.
Qed.

Lemma unfold_fib_co_acc_S :
  forall n' : nat,
    fib_co_acc (S n') = let (a1, a0) := fib_co_acc n'
                        in (a1 + a0, a1).
Proof.
  unfold_tactic fib_co_acc.
Qed.

(* Main definition: *)

Definition fib_v5 (n : nat) : nat :=
  let (a1, a0) := fib_co_acc n
  in a0.

Compute (test_fib fib_v5).

(* Associated unfold lemmas: *)

Lemma unfold_fib_v5 :
  forall n : nat,
    fib_v5 n =
    let (a1, a0) := fib_co_acc n
  in a0.
Proof.
  unfold_tactic fib_v5.
Qed.

(* Eureka lemma: *)

Lemma about_fib_co_acc :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      fib_co_acc n = (fib (S n), fib n).
Proof.
Abort.

(* The main definition satisfies the specification: *)

Theorem fib_v5_fits_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v5.
Proof.
Abort.

(* ********** *)

(* The fibonacci function with a co-accumulator in CPS: *)

Fixpoint fib_co_acc_cps (ans : Type) (n : nat) (k : nat * nat -> ans) : ans :=
  match n with
    | O =>
      k (1, 0)
    | S n' =>
      fib_co_acc_cps ans
                     n'
                     (fun p =>
                        match p with
                          | (a1, a0) =>
                            k (a1 + a0, a1)
                        end)
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_co_acc_cps_0 :
  forall (ans : Type)
         (k : nat * nat -> ans),
    fib_co_acc_cps ans 0 k = k (1, 0).
Proof.
  unfold_tactic fib_co_acc_cps.
Qed.

Lemma unfold_fib_co_acc_cps_S :
  forall (ans : Type)
         (n' : nat)
         (k : nat * nat -> ans),
    fib_co_acc_cps ans (S n') k =
    fib_co_acc_cps ans
                   n'
                   (fun p =>
                      match p with
                        | (a1, a0) =>
                          k (a1 + a0, a1)
                      end).
Proof.
  unfold_tactic fib_co_acc_cps.
Qed.

(* Main definition: *)

Definition fib_v6 (n : nat) : nat :=
  fib_co_acc_cps nat
                 n
                 (fun p =>
                    match p with
                    | (a1, a0) =>
                      a0
                    end).

Compute (test_fib fib_v6).

(* Associated unfold lemmas: *)

Lemma unfold_fib_v6_0 :
  fib_v6 0 = 0.
Proof.
  unfold_tactic fib_v6.
Qed.

Lemma unfold_fib_v6_S :
  forall n' : nat,
    fib_v6 (S n') =
    fib_co_acc_cps nat
                   n'
                   (fun p =>
                      match p with
                        | (a1, a0) =>
                          a1
                      end).
Proof.
  unfold_tactic fib_v6.
Qed.

(* Eureka lemma: *)

Lemma about_fib_co_acc_cps :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall (ans : Type)
           (n : nat)
           (k : nat * nat -> ans),
      fib_co_acc_cps ans n k =
      k (fib (S n), fib n).
Proof.
Abort.

(* The main definition satisfies the specification: *)

Theorem fib_v6_fits_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v6.
Proof.
Abort.

(* ********** *)

(* The fibonacci function with a co-accumulator in CPS with a curried continuation: *)

Fixpoint fib_co_acc_cps' (ans : Type) (n : nat) (k : nat -> nat -> ans) : ans :=
  match n with
    | O =>
      k 1 0
    | S n' =>
      fib_co_acc_cps' ans
                     n'
                     (fun a1 a0 =>
                        k (a1 + a0) a1)
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_co_acc_cps'_0 :
  forall (ans : Type)
         (k : nat -> nat -> ans),
    fib_co_acc_cps' ans 0 k = k 1 0.
Proof.
  unfold_tactic fib_co_acc_cps'.
Qed.

Lemma unfold_fib_co_acc_cps'_S :
  forall (ans : Type)
         (n' : nat)
         (k : nat -> nat -> ans),
    fib_co_acc_cps' ans (S n') k =
    fib_co_acc_cps' ans
                   n'
                   (fun a1 a0 =>
                      k (a1 + a0) a1).
Proof.
  unfold_tactic fib_co_acc_cps'.
Qed.

(* Main definition: *)

Definition fib_v7 (n : nat) : nat :=
  match n with
    | O => 0
    | S n' => 
      fib_co_acc_cps' nat
                     n'
                     (fun a1 a0 =>
                        a1)
  end.

Compute (test_fib fib_v7).

(* Associated unfold lemmas: *)

Lemma unfold_fib_v7_0 :
  fib_v7 0 = 0.
Proof.
  unfold_tactic fib_v7.
Qed.

Lemma unfold_fib_v7_S :
  forall n' : nat,
    fib_v7 (S n') =
    fib_co_acc_cps' nat
                   n'
                   (fun a1 a0 =>
                      a1).
Proof.
  unfold_tactic fib_v7.
Qed.

(* Eureka lemma: *)

Lemma about_fib_co_acc_cps' :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall (ans : Type)
           (n : nat)
           (k : nat -> nat -> ans),
      fib_co_acc_cps' ans n k =
      k (fib (S n)) (fib n).
Proof.
Abort.

(* The main definition satisfies the specification: *)

Theorem fib_v7_fits_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v7.
Proof.
Abort.

(* ********** *)

(* end of week-13_fib.v *)
