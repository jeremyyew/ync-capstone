(* week-15_a-commutative-diagram.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Spelled-out version of Sun 26 Nov 2017 *)
(* was: *)
(* Version of Sat 25 Nov 2017 *)

(* ********** *)

(*
   name: Jeremy Yew 
   student ID number: A0156262H
   e-mail address: jeremy.yew@u.yale-nus.edu.sg
*)

(* ********** *)
(*

The goal of this term project is to prove the following theorem:

  Theorem the_commutative_diagram :
    forall sp : source_program,
      interpret sp = run (compile sp).

for

* a source language of arithmetic expressions:

    Inductive arithmetic_expression : Type :=
    | Literal : nat -> arithmetic_expression
    | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
    | Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.
    
    Inductive source_program : Type :=
    | Source_program : arithmetic_expression -> source_program.

* a target language of byte-code instructions:

    Inductive byte_code_instruction : Type :=
    | PUSH : nat -> byte_code_instruction
    | ADD : byte_code_instruction
    | SUB : byte_code_instruction.
    
    Inductive target_program : Type :=
    | Target_program : list byte_code_instruction -> target_program.

* a semantics of expressible values:

    Inductive expressible_value : Type :=
    | Expressible_nat : nat -> expressible_value
    | Expressible_msg : string -> expressible_value.

The source for errors is subtraction,
since subtracting two natural numbers does not always yield a natural number:
for example, 3 - 2 is defined but not 2 - 3.

You are expected, at the very least:

* to implement a source interpreter
  and to verify that it satisfies its specification

* to implement a target interpreter (i.e., a virtual machine)
  and to verify that it satisfies its specification

* to implement a compiler
  and to verify that it satisfies its specification

* to prove that the diagram commutes, i.e., to show that
  interpreting any given expression
  gives the same result as
  compiling this expression and then running the resulting compiled program
  (to this end, the injection tactic illustrated in Lemma new_and_useful just below will come handy)

Beyond this absolute minimum, in decreasing importance, it would be good:

* to write an accumulator-based compiler and to prove that it satisfies the specification

* to investigate byte-code verification

* to revisit good old Magritte

* to write a continuation-based interpreter and to prove that it satisfies the specification

* to prove that each of the specifications specifies a unique function

*)

(* ********** *)

Lemma new_and_useful :
  forall i j : nat,
    Some i = Some j -> i = j.
Proof.
  intros i j H_Some.
  injection H_Some as H_i_j.  (* <--[new and useful]-- *)
  exact H_i_j.
Qed.

(* ********** *)

Ltac unfold_tactic name :=
  intros;
  unfold name; (* fold name; *)
  reflexivity.
  
Require Import Arith Bool List String.

Fixpoint ltb (n1 n2 : nat) : bool :=
  match n1 with
  | O =>
    match n2 with
    | O =>
      false
    | S n2' =>
      true
    end
  | S n1' =>
    match n2 with
    | O =>
      false
    | S n2' =>
      ltb n1' n2'
    end
  end.

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
| Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
| Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
| Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

(* ********** *)

Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
     evaluate (Literal n) = Expressible_nat n)
  /\
 ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       ltb n1 n2 = true ->
       evaluate (Minus ae1 ae2) = Expressible_msg "numerical underflow")
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       ltb n1 n2 = false ->
       evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2))).

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* Task 1: 
   prove that each of the definitions above specifies a unique function,
   implement these two functions,
   and verify that each of your functions satisfies its specification.
 *)

Theorem there_is_at_most_one_evaluate:
  forall f g : arithmetic_expression -> expressible_value,
    specification_of_evaluate f ->
    specification_of_evaluate g ->
    forall ae : arithmetic_expression,
      f ae = g ae.
Proof. 
  intros f g.
  intros [S_f_Literal
            [[S_f_Plus_msg [S_f_Plus_nat_msg S_f_Plus_nat_nat]]
               [S_f_Minus_msg [S_f_Minus_nat_msg
                                 [S_f_Minus_nat_nat_ltbt S_f_Minus_nat_nat_ltbf]]]]]
         [S_g_Literal
            [[S_g_Plus_msg [S_g_Plus_nat_msg S_g_Plus_nat_nat]]
               [S_g_Minus_msg [S_g_Minus_nat_msg
                                 [S_g_Minus_nat_nat_ltbt S_g_Minus_nat_nat_ltbf]]]]].
  intro ae.
  induction ae as [n
                  | ae1 IH_ae1 ae2 IH_ae2
                  | ae1 IH_ae1 ae2 IH_ae2].
  (*Literal*)
  rewrite -> S_f_Literal.
  rewrite -> S_g_Literal.
  reflexivity.

  (*Plus*)
  assert (H_g_ae1 := IH_ae1).
  assert (H_g_ae2 := IH_ae2).
  case (f ae1) as [n1 | s1] eqn: H_f_ae1.
  case (f ae2) as [n2 | s2] eqn: H_f_ae2.
  rewrite -> (S_f_Plus_nat_nat ae1 ae2 n1 n2 H_f_ae1 H_f_ae2).
  rewrite -> (S_g_Plus_nat_nat ae1 ae2 n1 n2).
  reflexivity.
  symmetry; apply H_g_ae1.
  symmetry; apply H_g_ae2.

  rewrite -> (S_f_Plus_nat_msg ae1 ae2 n1 s2 H_f_ae1 H_f_ae2).
  rewrite -> (S_g_Plus_nat_msg ae1 ae2 n1 s2).
  reflexivity.
  symmetry; apply H_g_ae1.
  symmetry; apply H_g_ae2.

  rewrite -> (S_f_Plus_msg ae1 ae2 s1 H_f_ae1).
  rewrite -> (S_g_Plus_msg ae1 ae2 s1).
  reflexivity.
  symmetry; apply H_g_ae1.

  (*Minus*)
  assert (H_g_ae1 := IH_ae1).
  assert (H_g_ae2 := IH_ae2).
  case (f ae1) as [n1 | s1] eqn: H_f_ae1.
  case (f ae2) as [n2 | s2] eqn: H_f_ae2.
  case (ltb n1 n2) as [ true | false ] eqn: H_ltb.
  rewrite -> (S_f_Minus_nat_nat_ltbt ae1 ae2 n1 n2 H_f_ae1 H_f_ae2 H_ltb).
  rewrite -> (S_g_Minus_nat_nat_ltbt ae1 ae2 n1 n2).
  reflexivity.
  symmetry; apply H_g_ae1.
  symmetry; apply H_g_ae2.
  apply H_ltb.
  
  rewrite -> (S_f_Minus_nat_nat_ltbf ae1 ae2 n1 n2 H_f_ae1 H_f_ae2 H_ltb).
  rewrite -> (S_g_Minus_nat_nat_ltbf ae1 ae2 n1 n2).
  reflexivity.
  symmetry; apply H_g_ae1.
  symmetry; apply H_g_ae2.
  apply H_ltb.
  
  rewrite -> (S_f_Minus_nat_msg ae1 ae2 n1 s2 H_f_ae1 H_f_ae2).
  rewrite -> (S_g_Minus_nat_msg ae1 ae2 n1 s2).
  reflexivity.
  symmetry; apply H_g_ae1.
  symmetry; apply H_g_ae2.
  rewrite -> (S_f_Minus_msg ae1 ae2 s1 H_f_ae1).
  rewrite -> (S_g_Minus_msg ae1 ae2 s1).
  reflexivity.
  symmetry; apply H_g_ae1.
Qed. 
  
Fixpoint evaluate (ae: arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
    Expressible_nat n
  | Plus ae1 ae2 =>
    match (evaluate ae1) with
    | Expressible_msg s1 =>
      Expressible_msg s1 
    | Expressible_nat n1 =>
      match (evaluate ae2) with
      | Expressible_msg s2 =>
        Expressible_msg s2
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      end
    end
  | Minus ae1 ae2 =>
    match (evaluate ae1) with
    | Expressible_msg s1 =>
      Expressible_msg s1
    | Expressible_nat n1 =>
      match (evaluate ae2) with
      | Expressible_msg s2 =>
        Expressible_msg s2
      | Expressible_nat n2 =>
        match (ltb n1 n2) with
        | true =>
          Expressible_msg "numerical underflow"
        | false =>
          Expressible_nat (n1 - n2)
        end
      end
    end
  end.

Lemma unfold_evaluate_Literal :
  forall n : nat,
    evaluate (Literal n) = Expressible_nat n.
Proof.
  unfold_tactic evaluate.
Qed.
  
Lemma unfold_evaluate_Plus :
  forall ae1 ae2 : arithmetic_expression,
    evaluate (Plus ae1 ae2) =
    match (evaluate ae1) with
    | Expressible_msg s1 =>
      Expressible_msg s1 
    | Expressible_nat n1 =>
      match (evaluate ae2) with
      | Expressible_msg s2 =>
        Expressible_msg s2
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      end
    end.
Proof.
  unfold_tactic evaluate.
Qed.

Lemma unfold_evaluate_Minus :
  forall ae1 ae2 : arithmetic_expression,
    evaluate (Minus ae1 ae2) =
    match (evaluate ae1) with
    | Expressible_msg s1 =>
      Expressible_msg s1
    | Expressible_nat n1 =>
      match (evaluate ae2) with
      | Expressible_msg s2 =>
        Expressible_msg s2
      | Expressible_nat n2 =>
        match (ltb n1 n2) with
        | true =>
          Expressible_msg "numerical underflow"
        | false =>
          Expressible_nat (n1 - n2)
        end
      end
    end.
Proof.
  unfold_tactic evaluate.
Qed.

Theorem there_is_at_least_one_evaluate:
  specification_of_evaluate evaluate.
Proof.
  unfold specification_of_evaluate.
  split.
    intro n.
    rewrite -> unfold_evaluate_Literal.
    reflexivity.
  split.
    split.
      intros ae1 ae2 s1 H_ae1_msg.
      rewrite -> unfold_evaluate_Plus.
      rewrite -> H_ae1_msg.
      reflexivity.
    split.
      intros ae1 ae2 n1 s2 H_ae1_nat H_ae2_msg. 
      rewrite -> unfold_evaluate_Plus.
      rewrite -> H_ae1_nat.
      rewrite -> H_ae2_msg.
      reflexivity.
    intros ae1 ae2 n1 n2 H_ae1_nat H_ae2_nat. 
    rewrite -> unfold_evaluate_Plus.
    rewrite -> H_ae1_nat.
    rewrite -> H_ae2_nat.
    reflexivity.
    split.
      intros ae1 ae2 s1 H_ae1_msg.
      rewrite -> unfold_evaluate_Minus.
      rewrite -> H_ae1_msg.
      reflexivity.
    split.
      intros ae1 ae2 n1 s2 H_ae1_nat H_ae2_msg. 
      rewrite -> unfold_evaluate_Minus.
      rewrite -> H_ae1_nat.
      rewrite -> H_ae2_msg.
      reflexivity.
    split.
      intros ae1 ae2 n1 n2 H_ae1_nat H_ae2_nat H_ltb_true. 
      rewrite -> unfold_evaluate_Minus.
      rewrite -> H_ae1_nat.
      rewrite -> H_ae2_nat.
      rewrite -> H_ltb_true.
      reflexivity.  
    intros ae1 ae2 n1 n2 H_ae1_nat H_ae2_nat H_ltb_false. 
    rewrite -> unfold_evaluate_Minus.
    rewrite -> H_ae1_nat.
    rewrite -> H_ae2_nat.
    rewrite -> H_ltb_false.
    reflexivity.  
Qed.  
 
Theorem there_is_at_most_one_interpret:
  forall f g : source_program -> expressible_value,
    specification_of_interpret f ->
    specification_of_interpret g ->
    forall sp : source_program,
      f sp = g sp.
Proof.
  intros f g.
  unfold specification_of_interpret.
  intros S_f S_g sp.
  case sp as [ae].
  rewrite -> (S_f evaluate there_is_at_least_one_evaluate).
  rewrite -> (S_g evaluate there_is_at_least_one_evaluate).
  reflexivity.
Qed.


Fixpoint interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae =>
    evaluate ae
  end.

Theorem there_is_at_least_one_interpret:
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret.
  intros evaluate S_evaluate ae.
  unfold interpret.
  apply there_is_at_most_one_evaluate.
  apply there_is_at_least_one_evaluate.
  apply S_evaluate.
Qed.
  
(* ********** *)

(* Task 2 (if there is time):
   Define an interpreter with a function in continuation-passing style
   that satisfies the specification above,
   and that only apply the current continuation to the result of evaluating
   an expression if evaluating this expression did not yield an error.
*)

(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
| PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

(* Target programs: *)

Inductive target_program : Type :=
| Target_program : list byte_code_instruction -> target_program.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
| OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition specification_of_decode_execute (decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  (forall (n : nat)
          (ds : data_stack),
     decode_execute (PUSH n) ds = OK (n :: ds))
  /\
  ((decode_execute ADD nil = KO "ADD: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute ADD (n2 :: nil) = KO "ADD: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       decode_execute ADD (n2 :: n1 :: ds) = OK ((n1 + n2) :: ds)))
  /\
  ((decode_execute SUB nil = KO "SUB: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute SUB (n2 :: nil) = KO "SUB: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       ltb n1 n2 = true ->
       decode_execute SUB (n2 :: n1 :: ds) = KO "numerical underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       ltb n1 n2 = false ->
       decode_execute SUB (n2 :: n1 :: ds) = OK ((n1 - n2) :: ds))).

(* Task 3:
   prove that the definition above specifies a unique function,
   implement this function,
   and verify that your function satisfies the specification.
*)
Theorem there_is_at_most_one_decode_execute :
    forall f g : byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_decode_execute f ->
    specification_of_decode_execute g ->
    forall (bci : byte_code_instruction) (ds : data_stack),
      f bci ds = g bci ds.
Proof. 
  intros f g.
  intros [S_f_PUSH
            [[S_f_ADD_nil [S_f_ADD_n2_nil S_f_ADD_n2_n1]]
               [S_f_SUB_nil [S_f_SUB_n2_nil
                                 [S_f_SUB_n2_n1_ltbt S_f_SUB_n2_n1_ltbf]]]]]
         [S_g_PUSH
            [[S_g_ADD_nil [S_g_ADD_n2_nil S_g_ADD_n2_n1]]
               [S_g_SUB_nil [S_g_SUB_n2_nil
                                 [S_g_SUB_n2_n1_ltbt S_g_SUB_n2_n1_ltbf]]]]].
  intros bci ds.
  induction bci as [ n | ADD | SUB ].

  (*PUSH*)
  rewrite -> S_f_PUSH.
  rewrite -> S_g_PUSH.
  reflexivity.

  (*ADD*)
  case ds as [nil| n2 ds'] eqn: H_ds.
  rewrite -> S_f_ADD_nil.
  rewrite -> S_g_ADD_nil.
  reflexivity.

  case ds' as [nil | n1 ds''] eqn: H_ds'.
  rewrite -> S_f_ADD_n2_nil.
  rewrite -> S_g_ADD_n2_nil.
  reflexivity.

  rewrite -> S_f_ADD_n2_n1.
  rewrite -> S_g_ADD_n2_n1.
  reflexivity.
  
  (*SUB*)
  case ds as [nil| n2 ds'] eqn: H_ds.
  rewrite -> S_f_SUB_nil.
  rewrite -> S_g_SUB_nil.
  reflexivity.

  case ds' as [nil | n1 ds''] eqn: H_ds'.
  rewrite -> S_f_SUB_n2_nil.
  rewrite -> S_g_SUB_n2_nil.
  reflexivity.

  case (ltb n1 n2) as [true | false ] eqn: H_ltb.
  rewrite -> (S_f_SUB_n2_n1_ltbt).
  rewrite -> S_g_SUB_n2_n1_ltbt.
  reflexivity.
  apply H_ltb.
  apply H_ltb.

  rewrite -> S_f_SUB_n2_n1_ltbf.
  rewrite -> S_g_SUB_n2_n1_ltbf.
  reflexivity.
  apply H_ltb.
  apply H_ltb.
Qed.  

Definition decode_execute (bci : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bci with
  | PUSH n =>
    OK (n :: ds)
  | ADD =>
    match ds with
    | nil =>
      KO "ADD: stack underflow"
    | n2 :: ds' =>
      match ds' with
      | nil =>
        KO "ADD: stack underflow"
      | n1 :: ds'' =>
        OK ((n1 + n2) :: ds'')
      end
    end
  | SUB =>
    match ds with
    | nil =>
      KO "SUB: stack underflow"
    | n2 :: ds' =>
      match ds' with
      | nil =>
        KO "SUB: stack underflow"
      | n1 :: ds'' =>
        match ltb n1 n2 with
        | true =>
          KO "numerical underflow"
        | false =>
          OK ((n1 - n2) :: ds'')
        end
      end
    end
  end.

Theorem decode_execute_satisfies_the_specification_of_decode_execute :
  specification_of_decode_execute decode_execute.
Proof.
  unfold specification_of_decode_execute.
  unfold decode_execute.  
  split.
    intros n ds.
    reflexivity.
  split.
    split.
      reflexivity.
    split.
      reflexivity.
    intros n1 n2 ds.
    reflexivity.
  split.
    reflexivity.
  split.
    reflexivity.  
  split.
    intros n1 n2 ds H_ltb.
    rewrite -> H_ltb.
    reflexivity.
  intros n1 n2 ds H_ltb.
  rewrite -> H_ltb.
  reflexivity.
Qed.

(* ********** *)

(* Specification of the virtual machine: *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  forall decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_decode_execute decode_execute ->
    (forall ds : data_stack,
        fetch_decode_execute_loop nil ds = OK ds)
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds ds' : data_stack),
        decode_execute bci ds = OK ds' ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        fetch_decode_execute_loop bcis' ds')
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds : data_stack)
            (s : string),
        decode_execute bci ds = KO s ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        KO s).

(* Task 4:
   prove that the definition above specifies a unique function,
   implement this function,
   and verify that your function satisfies the specification.
*)

Theorem there_is_at_most_one_fetch_decode_execute_loop:
    forall f g : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop f ->
    specification_of_fetch_decode_execute_loop g ->
    forall (bcis : list byte_code_instruction) (ds : data_stack),
      f bcis ds = g bcis ds.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intros f g S_f S_g bcis.
  destruct (S_f decode_execute decode_execute_satisfies_the_specification_of_decode_execute) as [S_f_nil [S_f_bci_OK S_f_bci_KO]].
  destruct (S_g decode_execute decode_execute_satisfies_the_specification_of_decode_execute) as [S_g_nil [S_g_bci_OK S_g_bci_KO]].

  induction bcis as [nil | bci bcis' IH_bcis].
  intro ds.
  rewrite -> S_f_nil.
  rewrite -> S_g_nil.
  reflexivity.

  intro ds.
  case (decode_execute bci ds) as [ds' | s] eqn : H_bci_ds.
  rewrite -> (S_f_bci_OK bci bcis' ds ds' H_bci_ds).
  rewrite -> (S_g_bci_OK bci bcis' ds ds' H_bci_ds).
  rewrite -> IH_bcis.
  reflexivity.

  rewrite -> (S_f_bci_KO bci bcis' ds s H_bci_ds).
  rewrite -> (S_g_bci_KO bci bcis' ds s H_bci_ds).
  reflexivity.
Qed.

Fixpoint fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | nil =>
    OK ds
  | bci :: bcis' =>
    match decode_execute bci ds with
    | OK ds' =>
      fetch_decode_execute_loop bcis' ds'
    | KO s =>
      KO s
    end
  end.

Lemma unfold_fetch_decode_execute_loop_nil:
  forall ds : data_stack,
    fetch_decode_execute_loop nil ds = OK ds.
Proof.
  unfold_tactic fetch_decode_execute_loop.
Qed.

Lemma unfold_fetch_decode_execute_loop_bcis:
  forall (bci : byte_code_instruction) (bcis' : list byte_code_instruction)
  (ds : data_stack),
    fetch_decode_execute_loop (bci :: bcis') ds =
    match decode_execute bci ds with
    | OK ds' =>
      fetch_decode_execute_loop bcis' ds'
    | KO s =>
      KO s
    end.
Proof.
  unfold_tactic fetch_decode_execute_loop.
Qed.
Theorem fetch_decode_execute_loop_satisfies_the_specification:
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intros decode_execute S_decode_execute.
  split.
    intro ds.
    rewrite -> unfold_fetch_decode_execute_loop_nil.
    reflexivity.
  split.
    intros bci bcis' ds ds' H_bci_ds_OK. 
    rewrite -> unfold_fetch_decode_execute_loop_bcis.
    rewrite -> (there_is_at_most_one_decode_execute Top.decode_execute decode_execute decode_execute_satisfies_the_specification_of_decode_execute S_decode_execute).
    rewrite -> (H_bci_ds_OK).
    reflexivity.
  intros bci bcis' ds ds' H_bci_ds_KO. 
  rewrite -> unfold_fetch_decode_execute_loop_bcis.
  rewrite -> (there_is_at_most_one_decode_execute Top.decode_execute decode_execute decode_execute_satisfies_the_specification_of_decode_execute S_decode_execute).
  rewrite -> (H_bci_ds_KO).
  reflexivity.
Qed.
  
  (* ********** *) 

(* Task 5:
   Prove that for any lists of byte-code instructions bcis1 and bcis2,
   and for any data stack ds,
   executing the concatenation of bcis1 and bcis2 (i.e., bcis1 ++ bcis2) with ds
   gives the same result as
   (1) executing bcis1 with ds, and then
   (2) executing bcis2 with the resulting data stack, if there exists one.
*)

Lemma unfold_append_nil :
  forall bcis2 : list byte_code_instruction,
    nil ++ bcis2 = bcis2.
Proof.
  unfold_tactic List.app.
Qed.

Lemma unfold_append_nil_r :
  forall bcis2 : list byte_code_instruction,
    bcis2 ++ nil = bcis2.
Proof.
  Admitted.

Lemma unfold_append_cons :
  forall (bci1 : byte_code_instruction)
         (bci1s bci2s : list byte_code_instruction),
    (bci1 :: bci1s) ++ bci2s =
    bci1 :: (bci1s ++ bci2s).
Proof.
  unfold_tactic List.app.
Qed.


Theorem fetch_decode_execute_loop_is_distributive_over_append :
  forall (bcis1 bcis2: list byte_code_instruction)(ds ds': data_stack),
    fetch_decode_execute_loop bcis1 ds = OK ds' ->
        fetch_decode_execute_loop (bcis1 ++ bcis2) ds
        =
        fetch_decode_execute_loop bcis2 (ds').
Proof.
  intros bcis1 bcis2.
  induction bcis1 as [nil | bci1 bci1s IH_bci1s].
  induction bcis2 as [nil | bci2 bci2s IH_bci2s].
  intros ds ds' H_bcis1_OK.
  rewrite -> unfold_append_nil.
  rewrite -> H_bcis1_OK.
  rewrite -> unfold_fetch_decode_execute_loop_nil at 1.
  reflexivity.
  
  intros ds ds' H_bcis_OK.
  rewrite -> unfold_append_nil.
  (*rewrite -> unfold_append_nil_r.
  rewrite -> H_bcis_OK.
  rewrite -> unfold_fetch_decode_execute_loop_nil at 1.
  reflexivity.
*)
Admitted.

Theorem fetch_decode_execute_loop_is_distributive_over_append' :
  forall (bcis1 bcis2: list byte_code_instruction)(ds : data_stack),
  exists ds': data_stack,
    fetch_decode_execute_loop bcis1 ds = OK ds' ->
        fetch_decode_execute_loop (bcis1 ++ bcis2) ds
        =
        fetch_decode_execute_loop bcis2 (ds').
Proof.
  intros bcis1 bcis2 ds.
  induction bcis1 as [nil | bci1 bci1s IH_bci1s].
  induction bcis2 as [nil | bci2 bci2s IH_bci2s].
  exists ds.
  intro H_bcis1_OK.
  rewrite -> unfold_append_nil.
  rewrite -> H_bcis1_OK.
  reflexivity.

  exists ds.
  intro H_bcis_OK.
  rewrite -> unfold_append_nil.
  reflexivity.

  destruct IH_bci1s as [ds' IH_bci1s].
  case (bci1) as [ | | ] eqn: H.
  exists (ds').
  intro H_bcis_OK.
  rewrite -> unfold_append_cons.
  rewrite -> unfold_fetch_decode_execute_loop_bcis.  
  rewrite -> unfold_fetch_decode_execute_loop_bcis in H_bcis_OK.
  
  Restart.
  intros bcis1 bcis2 ds.
  induction bcis2 as [nil | bci2 bci2s IH_bci2s].
  induction bcis1 as [nil | bci1 bci1s IH_bci1s].
  exists ds.
  intro H_bcis1_OK.
  rewrite -> unfold_append_nil.
  rewrite -> H_bcis1_OK.
  reflexivity.

  exists ds.
  intro H_bcis_OK.
  rewrite -> unfold_append_nil_r.
  rewrite -> H_bcis_OK.
  rewrite -> unfold_fetch_decode_execute_loop_nil at 1.
  reflexivity.

  destruct IH_bci2s as [ds' IH_bci2s].
  exists (ds').
  intro H_bcis_OK.
  assert (IH_bci2s_ds' := H_bcis_OK).
  apply IH_bci2s in IH_bci2s_ds'.
  rewrite -> unfold_fetch_decode_execute_loop_bcis.
Admitted.
  (* ********** *)

Definition specification_of_run (run : target_program -> expressible_value) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction),
       fetch_decode_execute_loop bcis nil = OK nil ->
       run (Target_program bcis) = Expressible_msg "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
       fetch_decode_execute_loop bcis nil = OK (n :: nil) ->
       run (Target_program bcis) = Expressible_nat n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
       fetch_decode_execute_loop bcis nil = OK (n :: n' :: ds'') ->
       run (Target_program bcis) = Expressible_msg "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop bcis nil = KO s ->
       run (Target_program bcis) = Expressible_msg s).

(* Task 6:
   prove that the definition above specifies a unique function,
   implement this function,
   and verify that your function satisfies the specification.
 *)

Theorem there_is_at_most_one_run:
  forall f g : target_program -> expressible_value,
    specification_of_run f ->
    specification_of_run g -> 
    forall (tp : target_program),
      f tp = g tp.
Proof.
  intros f g.
  intros S_f S_g tp.
  destruct (S_f fetch_decode_execute_loop) as [S_f_OK_nil [S_f_OK_n_nil [S_f_OK_n_n_ds S_f_KO]]].
  exact fetch_decode_execute_loop_satisfies_the_specification.
  destruct (S_g fetch_decode_execute_loop) as [S_g_OK_nil [S_g_OK_n_nil [S_g_OK_n_n_ds S_g_KO]]].
  exact fetch_decode_execute_loop_satisfies_the_specification.
  case tp as [bcis].

  case (fetch_decode_execute_loop bcis nil) as [nil | [ | n ]] eqn: H_bcis_nil.
  rewrite -> S_f_OK_nil.
  rewrite -> S_g_OK_nil.
  reflexivity.
  (*  exact H_bcis_nil.*)
Admitted.

  
Definition run (tp : target_program): expressible_value :=
  match tp with
  | Target_program bcis =>
    match (fetch_decode_execute_loop bcis nil) with
    | OK ds =>
      match ds with
      | nil =>
        Expressible_msg "no result on the data stack"
      | n :: ds' =>
        match ds' with
        | nil =>
          Expressible_nat n
        | n' :: ds'' =>
          Expressible_msg "too many results on the data stack"
        end
      end
    | KO s =>
      Expressible_msg s
    end
  end.  
        
Theorem run_satisfies_the_specification_of_run:
  specification_of_run run.
Proof.
  unfold specification_of_run.
  intros fetch_decode_execute_loop S_fetch_decode_execute_loop.
  split.
    intros bcis H_fetch_OK.
    unfold run.
    rewrite -> (there_is_at_most_one_fetch_decode_execute_loop Top.fetch_decode_execute_loop fetch_decode_execute_loop  fetch_decode_execute_loop_satisfies_the_specification S_fetch_decode_execute_loop).
    rewrite -> H_fetch_OK.
    reflexivity.
  split.
    intros bcis n H_fetch_OK. 
    unfold run.
    rewrite -> (there_is_at_most_one_fetch_decode_execute_loop Top.fetch_decode_execute_loop fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification S_fetch_decode_execute_loop).
    rewrite -> H_fetch_OK.
    reflexivity.
  split.
    intros bcis n n' ds'' H_fetch_OK. 
    unfold run.
    rewrite -> (there_is_at_most_one_fetch_decode_execute_loop Top.fetch_decode_execute_loop fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification S_fetch_decode_execute_loop).
    rewrite -> H_fetch_OK.
    reflexivity.
  intros bcis s H_fetch_KO. 
  unfold run.
  rewrite -> (there_is_at_most_one_fetch_decode_execute_loop Top.fetch_decode_execute_loop fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification S_fetch_decode_execute_loop).
  rewrite -> H_fetch_KO.
  reflexivity.
Qed.

  (* ********** *)

Definition specification_of_compile_aux (compile_aux : arithmetic_expression -> list byte_code_instruction) :=
  (forall n : nat,
     compile_aux (Literal n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)).

(* Task 6:
   prove that the definition above specifies a unique function,
   implement this function using list concatenation, i.e., ++,
   and verify that your function satisfies the specification.
 *)
Theorem there_is_at_most_one_compile_aux:
  forall f g : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux f ->
    specification_of_compile_aux g -> 
    forall (ae : arithmetic_expression),
      f ae = g ae.
Proof.
  intros f g.
  intros [S_f_Literal [S_f_Plus S_f_Minus]] [S_g_Literal [S_g_Plus S_g_Minus ]].
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  
  rewrite -> S_f_Literal.
  rewrite -> S_g_Literal.
  reflexivity.

  rewrite -> S_f_Plus.
  rewrite -> S_g_Plus.
  rewrite -> IHae1.
  rewrite -> IHae2.
  reflexivity.

  rewrite -> S_f_Minus.
  rewrite -> S_g_Minus.
  rewrite -> IHae1.
  rewrite -> IHae2.  
  reflexivity.
Qed.
  
Fixpoint compile_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
    PUSH n :: nil 
  | Plus ae1 ae2 =>
    (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil)
  | Minus ae1 ae2 =>
    (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)
  end.

Lemma unfold_compile_aux_Literal :
  forall n : nat,
    compile_aux (Literal n) = PUSH n :: nil.
Proof.
  unfold_tactic compile_aux.
Qed.

Lemma unfold_compile_aux_Plus :
  forall ae1 ae2 : arithmetic_expression,
    compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil).
Proof.
  unfold_tactic compile_aux.
Qed.

Lemma unfold_compile_aux_Minus :
  forall ae1 ae2 : arithmetic_expression,
    compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil).
Proof.
  unfold_tactic compile_aux.
Qed.

Theorem compile_aux_satisfies_the_specification_of_compile_aux :
  specification_of_compile_aux compile_aux. 
Proof.
  unfold specification_of_compile_aux.
  split.
    intro n.
    rewrite -> unfold_compile_aux_Literal.
    reflexivity.
  split.
  intros ae1 ae2.
  rewrite -> unfold_compile_aux_Plus.
  reflexivity.
  intros ae1 ae2.
  rewrite -> unfold_compile_aux_Minus.
  reflexivity.
Qed.  
  
Definition specification_of_compile (compile : source_program -> target_program) :=
  forall compile_aux : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall ae : arithmetic_expression,
      compile (Source_program ae) = Target_program (compile_aux ae).

(* Task 7:
   prove that the definition above specifies a unique function,
   implement this function,
   and verify that your function satisfies the specification.
 *)

Theorem there_is_at_most_one_compile:
  forall f g : source_program -> target_program,
    specification_of_compile f ->
    specification_of_compile g -> 
    forall (sp : source_program),
      f sp = g sp.
Proof.
  intros f g.
  unfold specification_of_compile.
  intros S_f S_g sp.
  case sp as [ae].
  rewrite -> (S_f compile_aux compile_aux_satisfies_the_specification_of_compile_aux). 
  rewrite -> (S_g compile_aux compile_aux_satisfies_the_specification_of_compile_aux). 
  reflexivity.
Qed.
  
Fixpoint compile (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
    Target_program (compile_aux ae)
  end.

Theorem compile_satisfies_the_specification_of_compile :
  specification_of_compile compile. 
Proof.
  unfold specification_of_compile.
  intros compile_aux S_compile_aux ae.
  unfold compile.
  rewrite -> (there_is_at_most_one_compile_aux Top.compile_aux compile_aux compile_aux_satisfies_the_specification_of_compile_aux S_compile_aux).
  reflexivity.
Qed.


(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.
*)

(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
 *)

(* Lemma new_and_useful :
  forall i j : nat,
    Some i = Some j -> i = j.
Proof.
  intros i j H_Some.
  injection H_Some as H_i_j.  (* <--[new and useful]-- *)
  exact H_i_j.
Qed.*)

Lemma Expressible_n1_n2 :
  forall n1 n2 : nat,
    Expressible_nat n1 = Expressible_nat n2
    ->
    n1 = n2.
Proof.
  intros n1 n2 H_Expressible_nat.
  injection H_Expressible_nat as H_i_j.
  exact H_i_j.
Qed.

Theorem the_commutative_diagram :
  forall sp : source_program,
    interpret sp = run (compile sp).
Proof.
  intro sp.
  case sp as [ae].
  unfold interpret.
  unfold compile.
  unfold run.
(*forall ae, forall ds, a relation between (evaluate ae) and (fetch_decode_execute_loop compile_aux ae) ds).  *)
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ].
  
  rewrite -> unfold_evaluate_Literal.
  rewrite -> unfold_compile_aux_Literal.
  unfold run.
  rewrite -> unfold_fetch_decode_execute_loop_bcis.
  unfold decode_execute.
  rewrite -> unfold_fetch_decode_execute_loop_nil.
  reflexivity.

  rewrite -> unfold_evaluate_Plus.
  case (evaluate ae1) as [n1 | s1] eqn : H_eval_ae1.
  case (evaluate ae2) as [n2 | s2] eqn : H_eval_ae2.
Abort. 
  
  (* ********** *)

(* Task 10 (if there is time):

   a. Write a Magritte interpreter for the source language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   b. Write a Magritte interpreter for the target language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   c. Prove that interpreting an arithmetic expression with the Magritte source interpreter
      gives the same result as first compiling it and then executing the compiled program
      with the Magritte target interpreter over an empty data stack.

   d. Prove that the Magritte target interpreter is (essentially)
      a left inverse of the compiler, i.e., it is a decompiler.
*)

(* ********** *)

(* Byte-code verification:
   the following verifier symbolically executes a byte-code program
   to check whether no underflow occurs during execution
   and whether when the program completes,
   there is one and one only natural number on top of the stack.
   The second argument of verify_aux is a natural number
   that represents the size of the stack.
*)

Fixpoint verify_aux (bcis : list byte_code_instruction) (n : nat) : option nat :=
  match bcis with
    | nil =>
      Some n
    | bci :: bcis' =>
      match bci with
        | PUSH _ =>
          verify_aux bcis' (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis' (S n')
            | _ =>
              None
          end
      end
  end.

Definition verify (p : target_program) : bool :=
  match p with
  | Target_program bcis =>
    match verify_aux bcis 0 with
    | Some n =>
      match n with
      | 1 =>
        true
      | _ =>
        false
      end
    | _ =>
      false
    end
  end.

(* Task 11:
   Prove that the compiler emits code
   that is accepted by the verifier.
*)

(*
Theorem the_compiler_emits_well_behaved_code :
  forall ae : arithmetic_expression,
    verify (compile ae) = true.
Proof.
Abort.
*)

(* What are the consequences of this theorem? *)

(* ********** *)

(* end of week-15_a-commutative-diagram.v *)
