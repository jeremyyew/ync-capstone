(* week-02_backward-and-forward.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 25 Aug 2017 *)

(* ***********)

(* Learning goals:

   * using assert to declare a new assumption

   * using apply among the assumptions
*)

(* ********** *)

(* Prove foo:

   (1) backward, in a goal-directed way

   (2) forward, from the assumptions
*)

Proposition foo :
  forall P Q R1 R2 : Prop,
    P -> (P -> Q) -> (Q -> R1) /\ (Q -> R2) -> R1 /\ R2.
Proof.
  intros P Q R1 R2.
  intros H_P H_P_implies_Q [H_Q_implies_R1 H_Q_implies_R2].

  split.

  apply H_Q_implies_R1.
  apply H_P_implies_Q.
  apply H_P.

  apply H_Q_implies_R2.
  apply H_P_implies_Q.
  apply H_P.

  Restart.

  intros P Q R1 R2.
  intros H_P H_P_implies_Q [H_Q_implies_R1 H_Q_implies_R2].

  assert (H1 := H_P).
  apply H_P_implies_Q in H1.
  apply H_Q_implies_R1 in H1.
  assert (H2 := H_P).
  apply H_P_implies_Q in H2.
  apply H_Q_implies_R2 in H2.
  split.
    apply H1.
  apply H2.
Qed.

(* ********** *)

(* Prove bar:

   (1) by using the split tactic as early as possible 

   (2) by using the split tactic as late as possible 
*)

Proposition bar :
  forall P1 P2 Q R1 R2 T1 T2 : Prop,
    P1 -> (P1 -> P2) -> (P2 -> Q) -> (Q -> R1) -> (R1 -> T1) -> (Q -> R2) -> (R2 -> T2) -> T1 /\ T2.
Proof.

  (* Here, use the split tactic as early as possible. *)
  intros P1 P2 Q R1 R2 T1 T2.
  intros H_P1 H_P1_implies_P2 H_P2_implies_Q H_Q_implies_R1 H_R1_implies_T1 H_Q_implies_R2 H_R2_implies_T2.

  split.
  
  apply H_R1_implies_T1.
  apply H_Q_implies_R1.
  apply H_P2_implies_Q.
  apply H_P1_implies_P2.
  apply H_P1.

  apply H_R2_implies_T2.
  apply H_Q_implies_R2. 
  apply H_P2_implies_Q.
  apply H_P1_implies_P2.
  apply H_P1.
  

  Restart.
  (* Here, use the split tactic as late as possible. *)
  
  intros P1 P2 Q R1 R2 T1 T2.
  intros H_P1 H_P1_implies_P2 H_P2_implies_Q H_Q_implies_R1 H_R1_implies_T1 H_Q_implies_R2 H_R2_implies_T2.

  assert (H1 := H_P1).
  apply H_P1_implies_P2 in H1.
  apply H_P2_implies_Q in H1.
  apply H_Q_implies_R1 in H1.
  apply H_R1_implies_T1 in H1.

  assert (H2 := H_P1).
  apply H_P1_implies_P2 in H2.
  apply H_P2_implies_Q in H2.
  apply H_Q_implies_R2 in H2.
  apply H_R2_implies_T2 in H2.

  split.
    apply H1.
  apply H2.
  
  
Abort.

(* ********** *)

(* Prove baz:

   (1) by using the split tactic as early as possible 

   (2) by using the split tactic as late as possible 
*)

Proposition baz :
  forall P Q R T U1 U2 : Prop,
    P -> (P -> Q) -> (Q -> R) -> (R -> T) -> (T -> U1) -> (T -> U2) -> U1 /\ U2.
Proof.
  intros P Q R T U1 U2.
  intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2.

  (* Here, use the split tactic as early as possible. *)

  split. 

  apply H_T_implies_U1.
  apply H_R_implies_T.
  apply H_Q_implies_R.
  apply H_P_implies_Q. 
  apply H_P.

  apply H_T_implies_U2.
  apply H_R_implies_T.
  apply H_Q_implies_R.
  apply H_P_implies_Q.
  apply H_P.
  
  Restart.

  (* Here, use the split tactic as early as possible. *)

  intros P Q R T U1 U2.
  intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2.

  assert (H1 := H_P).
  apply H_P_implies_Q in H1.
  apply H_Q_implies_R in H1.
  apply H_R_implies_T in H1.
  assert (H2 := H1).

  apply H_T_implies_U1 in H1. 
  apply H_T_implies_U2 in H2.

  split. 
    apply H1.
  apply H2.
Abort.

(* ********** *)

(* Complete the proofs of baz_dual,
   and then compare them.
*)

Proposition baz_dual_early :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros H_P1_or_P2 H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  (* use "destruct H_P1_or_P2 as [H_P1 | H_P2]." as early as you can *)

  destruct H_P1_or_P2 as [H_P1 | H_P2].

  apply H_T_implies_U.
  apply H_R_implies_T.
  apply H_Q_implies_R.
  apply H_P1_implies_Q.
  apply H_P1.

  apply H_T_implies_U.
  apply H_R_implies_T.
  apply H_Q_implies_R.
  apply H_P2_implies_Q.
  apply H_P2.

Abort.

Proposition baz_dual_late :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros H_P1_or_P2 H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.

  (* use "destruct H_P1_or_P2 as [H_P1 | H_P2]." as late as you can *)
  apply H_T_implies_U.
  apply H_R_implies_T.
  apply H_Q_implies_R. 

  
Abort.

(* Complete the following proof.
   What do you end up with?
   A proof close to that of Proposition baz_dual_early,
   or to that of Proposition baz_dual_late?
   What do you conclude?
*)
Proposition baz_dual_early_or_late :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros [H_P1 | H_P2] H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.

Abort.

(* ********** *)

(* How would you prove the following propositions?
   Forward or backward?
*)

Proposition ladidah :
  forall P1 P2 P3 P4 Q R T U : Prop,
    (P1 \/ P2) \/ (P3 \/ P4) -> (P1 -> Q) -> (P2 -> Q) -> (P3 -> Q) -> (P4 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Abort.

Proposition toodeloo :
  forall P Q R T U1 U2 U3 U4: Prop,
    P -> (P -> Q) -> (Q -> R) -> (R -> T) -> (T -> U1) -> (T -> U2) -> (T -> U3) -> (T -> U4) -> (U1 /\ U2) /\ (U3 /\ U4).
Abort.

(* How complex could the size of such proofs be
   (relative to the number of hypotheses P1, P2, P3, etc.
   and to the number of conclusions U1, U2, U3, etc.)?
*)

(* ***********)

(* end of week-02_backward-and-forward.v *)
