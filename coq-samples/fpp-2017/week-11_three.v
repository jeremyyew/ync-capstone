(* week-12_isometries3.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 31 Oct 2017 *)

(* A formal study of isometries of the equilateral triangle, *)
(* after Chantal Keller, Damien Pous and Sylvain Chevillard. *)

(* ********** *)

Inductive Rotation : Type :=
| R0   : Rotation  (* 0 degrees (identity) *)
| R120 : Rotation  (* 120 degrees *)
| R240 : Rotation. (* 240 degrees *)

(* ********** *)

(* Performing two rotations in a row, clockwise: *)
(* as it happens, the result is always a rotation. *)
(* "RaR" stands for "a Rotation after a Rotation" *)

Definition RaR (r2 r1: Rotation) : Rotation :=
  match r1 with
    | R0   => (* r2 *)
              match r2 with
                | R0   => R0
                | R120 => R120
                | R240 => R240
              end
    | R120 => match r2 with
                | R0   => R120
                | R120 => R240
                | R240 => R0
              end
    | R240 => match r2 with
                | R0   => R240
                | R120 => R0
                | R240 => R120
            end
  end.

(* Some properties: *)

Proposition R0_is_neutral_for_RaR_on_the_left :
  forall r : Rotation,
    RaR R0 r = r.
Proof.
  intro r; unfold RaR.
  case r as [ | | ] eqn:H_r.
  reflexivity.  
  reflexivity.  
  reflexivity.  
  Show Proof.

  Restart.

  intro r; unfold RaR.
  case r as [ | | ] eqn:H_r; reflexivity.  
  Show Proof.

  Restart.

  intro r; unfold RaR; case r as [ | | ] eqn:H_r; reflexivity.  

  Restart.

  intro r; case r as [ | | ] eqn:H_r; reflexivity.  

  Restart.

  intros [ | | ]; reflexivity.  
Qed.


Proposition R0_is_neutral_for_RaR_on_the_right :
  forall r : Rotation,
    RaR r R0 = r.
Proof.
  intros [ | | ]; reflexivity.
Qed.

Proposition RaR_is_commutative :
  forall r1 r2 : Rotation,
    RaR r2 r1 = RaR r1 r2.
Proof.
Admitted.

Proposition RaR_is_associative :
  forall r1 r2 r3 : Rotation,
    RaR (RaR r3 r2) r1 = RaR r3 (RaR r2 r1).
Proof.
Admitted.

Proposition RaR_is_nilpotent_with_order_3 :
  forall r : Rotation,
    RaR (RaR r r) r = R0.
Proof.
Admitted.

(* ********** *)

(* The following symmetries are indexed by the invariant vertex: *)

Inductive Reflection : Type :=
| S_N  : Reflection  (* North, at the top *)
| S_SW : Reflection (* South-West, at the bottom-left *)
| S_SE : Reflection.  (* South-East, at the bottom-right *)

(* These reflections are symmetries here. *)

(* Performing two reflections in a row: *)
(* as it happens, the result is always a rotation. *)
(* "SaS" stands for "a Symmetry after a Symmetry" *)

Definition SaS (s2 s1 : Reflection) : Rotation :=
  match s1 with
    | S_N  => match s2 with
                | S_N  => R0
                | S_SW => R240
                | S_SE => R120
              end
    | S_SW => match s2 with
                | S_N  => R120
                | S_SW => R0
                | S_SE => R240
              end
    | S_SE => match s2 with
                | S_N  => R240
                | S_SW => R120
                | S_SE => R0
              end
  end.

(* is SaS commutative? *)
(* is SaS associative? *)
(* is SaS nilpotent?   *)

(* Performing a rotation and then a reflection in a row: *)
(* "SaR" stands for "a Symmetry after a Rotation" *)

Definition SaR (s : Reflection) (r : Rotation) : Reflection :=
  match r with
    | R0   => match s with
                | S_N  => S_N
                | S_SW => S_SW
                | S_SE => S_SE
              end
    | R120 => match s with
                | S_N  => S_SW
                | S_SW => S_SE
                | S_SE => S_N
              end
    | R240 => match s with
                | S_N  => S_SE
                | S_SW => S_N
                | S_SE => S_SW
              end
  end.

(* Performing a reflection and then a rotation in a row: *)
(* "RaS" stands for "a Rotation after a Symmetry" *)

Definition RaS (r : Rotation) (s : Reflection) : Reflection :=
  match s with
    | S_N => match r with
              | R0   => S_N
              | R120 => S_SE
              | R240 => S_SW
             end
    | S_SW => match r with
              | R0   => S_SW
              | R120 => S_N
              | R240 => S_SE
            end
    | S_SE => match r with
              | R0   => S_SE
              | R120 => S_SW
              | R240 => S_N
            end
  end.

(* ********** *)

Inductive Isomorphism : Type :=
| IR : Rotation -> Isomorphism
| IS : Reflection -> Isomorphism.

(* Identity: *)

Definition Id : Isomorphism := IR R0.

(* Composition: *)

Definition C (i2 i1 : Isomorphism) : Isomorphism :=
  match i1 with
    | IR r1 => match i2 with
                 | IR r2 => IR (RaR r2 r1)
                 | IS s2 => IS (SaR s2 r1)
               end
    | IS s1 => match i2 with
                 | IR r2 => IS (RaS r2 s1)
                 | IS s2 => IR (SaS s2 s1)
               end
  end.

Proposition Id_is_neutral_on_the_left_of_C :
  forall i : Isomorphism,
    C Id i = i.
Proof.
Admitted.

Proposition Id_is_neutral_on_the_right_of_C :
  forall i : Isomorphism,
    C i Id = i.
Proof.
Admitted.

Proposition C_is_associative :
  forall i1 i2 i3 : Isomorphism,
    C i3 (C i2 i1) = C (C i3 i2) i1.
Proof.
Admitted.

Lemma composing_an_isomorphism_is_injective_on_the_right :
  forall i x y : Isomorphism,
    C i x = C i y -> x = y.
Proof.
  intros [[ | | ] | [ | | ]]
         [[ | | ] | [ | | ]]
         [[ | | ] | [ | | ]]
         H;
    (reflexivity || discriminate H).

  Restart.

  intros [[ | | ] | [ | | ]]
         [[ | | ] | [ | | ]]
         [[ | | ] | [ | | ]];
    (reflexivity || intro H); discriminate H.
Qed.

Lemma composing_an_isomorphism_is_injective_on_the_left :
  forall i x y : Isomorphism,
    C x i = C y i -> x = y.
Proof.
  intros [[ | | ] | [ | | ]]
         [[ | | ] | [ | | ]]
         [[ | | ] | [ | | ]];
    (reflexivity || intro H); discriminate H.
Qed.

Lemma composing_an_isomorphism_is_surjective_on_the_right :
  forall i2 i3 : Isomorphism,
    exists i1 : Isomorphism,
      C i2 i1 = i3.
Proof.
  intros [[ | | ] | [ | | ]]
         [[ | | ] | [ | | ]];
    ((exists (IR R0); reflexivity) ||
     (exists (IR R120); reflexivity) ||
     (exists (IR R240); reflexivity) ||
     (exists (IS S_N); reflexivity) ||
     (exists (IS S_SE); reflexivity) ||
     (exists (IS S_SW); reflexivity)).
Qed.

Lemma composing_an_isomorphism_is_surjective_on_the_left :
  forall i1 i3 : Isomorphism,
    exists i2 : Isomorphism,
      C i2 i1 = i3.
Proof.
Admitted.

Proposition C_over_rotations_is_nilpotent_with_order_3 :
  forall r : Rotation,
    C (C (IR r) (IR r)) (IR r) = Id.
Proof.
Admitted.

Proposition C_over_symmetries_is_nilpotent_with_order_2 :
  forall s : Reflection,
    C (IS s) (IS s) = Id.
Proof.
  intros [ | | ]; reflexivity.

  Restart.

  (* Instead of using brute force,
     use SaS_is_nilpotent_with_order_2 *)
Admitted.

(* 6 is the least common multiple of 2 and 3: *)

Proposition C_is_nilpotent_with_order_6 :
  forall i : Isomorphism,
    C (C (C (C (C i i) i) i) i) i
    =
    Id.
Proof.
  intros [[ ] | [ ]]; reflexivity.

  Restart.

  (* Instead of using brute force,
     use the two previous propositions. *)
Admitted.

(* ********** *)

(* Let us now introduce the vertices: *)

Inductive Vertex : Type := (* enumerated clockwise *)
| N  : Vertex
| SW : Vertex
| SE : Vertex.

(* And let us define the effect of applying an isomorphism
   to a vertex: *)

Definition A (i : Isomorphism) (v : Vertex) : Vertex :=
  match i with
    | IR r => match r with
                | R0   => match v with
                            | N  => N
                            | SW => SW
                            | SE => SE
                          end
                | R120 => match v with
                            | N  => SW
                            | SW => SE
                            | SE => N
                          end
                | R240 => match v with
                            | N  => SE
                            | SE => SW
                            | SW => N
                          end
              end
    | IS s => match s with
                | S_N  => match v with
                            | N  => N
                            | SW => SE
                            | SE => SW
                          end
                | S_SE => match v with
                            | N  => SW
                            | SW => N
                            | SE => SE
                          end
                | S_SW => match v with
                            | N  => SE
                            | SW => SW
                            | SE => N
                          end
              end
  end.

Proposition A_is_equivalent_to_C :
  forall (i1 i2 : Isomorphism) (v : Vertex),
    A i2 (A i1 v) = A (C i2 i1) v.
Proof.
Admitted.

Proposition applying_an_isomorphism_is_injective :
  forall (i : Isomorphism) (v1 v2 : Vertex),
    (A i v1 = A i v2) -> v1 = v2.
Proof.
Admitted.

Proposition applying_an_isomorphism_is_surjective :
  forall (i : Isomorphism) (v2 : Vertex),
    exists v1 : Vertex,
      A i v1 = v2.
Proof.
Admitted.

(* ********** *)

(* Intensional equality:
   two isomorphisms are equal
   iff
   they are are constructed alike.
 *)

Definition intensional_equality (i1 i2: Isomorphism) : Prop :=
  i1 = i2.

(* Extensional equality:
   two isomorphisms are equal
   iff
   their graphs are the same.
 *)

Definition extensional_equality (i1 i2: Isomorphism) : Prop :=
  forall v : Vertex,
    A i1 v = A i2 v.

(* The two notions of equalities coincide: *)

Proposition the_two_equalities_are_the_same :
  forall i1 i2 : Isomorphism,
    intensional_equality i1 i2 <-> extensional_equality i1 i2.
Proof.
Admitted.

(* ********** *)

Lemma isomorphism_equality_in_context_on_the_left :
  forall x y i : Isomorphism,
    x = y -> C x i = C y i.
Proof.
Admitted.

Proposition take_five :
  forall i : Isomorphism,
    extensional_equality (C (C (C (C i i) i) i) i) Id
    ->
    i = Id.
Proof.
  unfold extensional_equality, Id.
  intros [[ | | ] | [ | | ]] H_ee;
    (reflexivity ||
     discriminate (H_ee N) ||
     discriminate (H_ee SE) ||
     discriminate (H_ee SW)).

  Restart.

  (* Instead of using brute force,
     use C_is_nilpotent_with_order_6. *)
Admitted.

Proposition characteristic_property_of_Id :
  forall i : Isomorphism,
    i = Id <-> forall v : Vertex, A i v = v.
Proof.
Admitted.

Proposition one_for_the_road :
  forall i : Isomorphism,
    (forall v : Vertex, A i v = v)
    ->
    C i i = Id.
Proof.
  unfold Id.
  intros [[ | | ] | [ | | ]] H_A;
    (reflexivity ||
     discriminate (H_A N) ||
     discriminate (H_A SE) ||
     discriminate (H_A SW)).

  Restart.

  (* Instead of using brute force,
     use the previous proposition. *)
Admitted.

Proposition notable_property_of_Id :
  exists i : Isomorphism,
    exists v : Vertex,
      not (A i v = v -> i = Id).
Proof.
Admitted.

Proposition notable_property_of_Id' :
  not (forall (i : Isomorphism) (v : Vertex),
         A i v = v -> i = Id).
Proof.
Admitted.

Proposition notable_property_of_symmetries :
  forall (i : Isomorphism)
         (v : Vertex),
    A i v = v ->
    ((i = IR R0)
     \/
     (exists s : Reflection,
        i = IS s)).
Proof.
Admitted.

Proposition notable_property_of_symmetries' :
  forall i : Isomorphism,
    (exists v : Vertex,
       A i v = v) ->
    ((i = IR R0)
     \/
     (exists s : Reflection,
        i = IS s)).
Proof.
Admitted.

Proposition one_more_for_the_road :
  forall (i : Isomorphism) (v : Vertex),
    A i v = v -> C i i = Id.
Proof.
  unfold Id.
  intros [[ | | ] | [ | | ]] [ | | ] H_A;
    (reflexivity || discriminate H_A).

  Restart.

  (* Instead of using brute force,
     find another proof. *)
Admitted.

(* ********** *)

(* end of week-12_isometries3.v *)