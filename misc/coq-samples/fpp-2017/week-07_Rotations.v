Inductive Rotation : Type :=
| R0 : Rotation
| R120 : Rotation
| R240 : Rotation.

Definition RaR (r2 r1 : Rotation) : Rotation:=
  match r1 with
  |R0 =>
     (match r2 with
     |R0 => R0
     |R120 => R120
     |R240 => R240
      end)
  |R120 =>
     (match r2 with
     |R0 => R120
     |R120 => R240
     |R240 => R0
      end)
  |R240 =>
     (match r2 with
     |R0 => R240
     |R120 => R0
     |R240 => R120 
      end)
  end.

Proposition R0_is_neutral_for_RaR_on_the_left:
  forall (r : Rotation),
    RaR R0 r = r.
Proof.
  intro r.
  induction r.
  unfold RaR.
  reflexivity.

  unfold RaR.
  reflexivity.
  
  unfold RaR.
  reflexivity.

  Restart.
  intro r.
  case r as [ | | ] eqn: H_r.

  unfold RaR; reflexivity.

  unfold RaR; reflexivity.

  unfold RaR; reflexivity.

  Restart.
  intro r; case r as [ | | ] eqn: H_r; unfold RaR; reflexivity.

  Restart.
  intros [ | | ]; unfold RaR; reflexivity.

  Restart.
  intros [ | | ]; reflexivity.  
  (* 
We can unfold without writing unfold lemmas because RaR is not recursive.
   *) 
Qed.


Proposition R0_is_neutral_for_RaR_on_the_right:
  forall (r : Rotation),
    RaR R0 r = r.
Proof.
  intros [ | | ]; reflexivity.
Qed.

Proposition RaR_is_commutative:
  forall r1 r2: Rotation,
    RaR r2 r1 = RaR r1 r2.
Proof.
  intros r1 r2.
  case r1 as [ | | ] eqn: H_r1.
  case r2 as [ | | ] eqn: H_r2.
  reflexivity.

  unfold RaR.
  reflexivity.

  unfold RaR.
  reflexivity.

  unfold RaR.
  reflexivity.

  unfold RaR.
  reflexivity.

  Restart.
  intros [ | | ] [ | | ]; reflexivity.

Qed.

  
Proposition RaR_is_associative:
  forall r1 r2 r3: Rotation,
    RaR (RaR r3 r2) r1 = RaR r3 (RaR r2 r1).
Proof.
  intros [ | | ] [ | | ] [ | | ]; reflexivity.
Qed.

Proposition RaR_is_nilpotent_with_order_3:
  forall r : Rotation,
    RaR (RaR r r) r = R0.
Proof.
  intros [ | | ]; reflexivity.
Qed.

Inductive Reflection: Type :=
| S_N : Reflection
| S_SW : Reflection
| S_SE : Reflection.

Definition SaS (s2 s1: Reflection) :=
   match s1 with
  |S_N =>
     (match s2 with
     |S_N => R0
     |S_SW => R120
     |S_SE => R240
      end)
  |S_SW =>
     (match s2 with
     |S_N => R240
     |S_SW => R0
     |S_SE => R120
      end)
  |S_SE =>
     (match s2 with
     |S_N => R120
     |S_SW => R240
     |S_SE => R0 
      end)
  end.

Proposition SaS_is_commutative:
  forall s1 s2 : Reflection,
  SaS s1 s2 = SaS s2 s1.
Proof.
  (*
  intros [ | | ] [ | | ]; reflexivity.
   *)
  intros s1 s2.
  case s1 as [ | | ] eqn: H_s1.
  case s2 as [ | | ] eqn: H_s2.

  reflexivity.
  unfold SaS.
Abort.

Proposition SaS_is_not_commutative:
  exists s1 s2 : Reflection,
    (SaS s1 s2 <> SaS s2 s1).
Proof.
  exists S_SW, S_SE.
  unfold SaS.
  intro H_absurd.
  discriminate.
Qed.
(*
Proposition SaS_is_associative:
  forall s1 s2 : Reflection,
  SaS (SaS s3 s2) s1 = SaS s3 (SaS s2 s1).
  Proof.
This is type incorrect, as the codomain of SaS is a Rotation, and not a Reflection. 
 *)

Proposition SaS_is_nilpotent_with_order_2:
  forall s : Reflection,
    SaS s s = R0.
Proof.
  intros [ | | ]; reflexivity.
Qed.

Definition SaR (s : Reflection) (r : Rotation): Reflection :=
   match r with
  |R0 =>
     (match s with
     |S_N => S_N
     |S_SW => S_SW
     |S_SE => S_SE
      end)
  |R120 =>
     (match s with
     |S_N => S_SE 
     |S_SW => S_N
     |S_SE => S_SW
      end)
  |R240 =>
     (match s with
     |S_N => S_SW
     |S_SW => S_SE
     |S_SE => S_N
      end)
  end.


Definition RaS (r : Rotation) (s : Reflection): Reflection :=
   match s with
  |S_N =>
     (match r with
     |R0 => S_N
     |R120 => S_SE
     |R240 => S_SW
      end)
  |S_SW =>
     (match r with
     |R0 => S_SW
     |R120 => S_N
     |R240 => S_SE
      end)
  |S_SE =>
     (match r with
     |R0 => S_SE
     |R120 => S_SW
     |R240 => S_N
      end)
  end.

Inductive Isomorphism : Type :=
| IR : Rotation -> Isomorphism
| IS : Reflection -> Isomorphism.

Definition Id : Isomorphism := IR R0.

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

Proposition Id_is_neutral_for_C_on_the_left :
  forall i : Isomorphism,
    C Id i = i.
Proof.
  intros [ [ | | ] | [ | | ] ]. 
  unfold C.
  unfold Id.
  unfold RaR.
  reflexivity.
  Restart.

  intro i.
  unfold Id.
  unfold C.
  case i as [r| s] eqn: H_i.

  case r as [ | | ] eqn: H_r.
  unfold RaR.
  reflexivity.
  unfold RaR.
  reflexivity.
  unfold RaR.
  reflexivity.
  unfold RaR.
  Restart.
  
  intros [ [ | | ] | [ | | ] ]; reflexivity.
Qed.

Proposition Id_is_neutral_for_C_on_the_right :
  forall i : Isomorphism,
    C i Id = i.
Proof.
   intros [ [ | | ] | [ | | ] ]; reflexivity.
Qed.


Proposition C_is_associative:
  forall i1 i2 i3 : Isomorphism,
    C (C i3 i2) i1 = C i3 (C i2 i1).
Proof.
  intros i1 i2 i3.
  case i1 as [ [ | | ] | [ | | ] ] eqn:H_1.
  case i2 as [ [ | | ] | [ | | ] ] eqn:H_2. 
  case i3 as [ [ | | ] | [ | | ] ] eqn:H_3.
  
  unfold C, SaS, SaR, RaS, RaR; reflexivity.
  unfold C, SaS, SaR, RaS, RaR; reflexivity.
  unfold C, SaS, SaR, RaS, RaR; reflexivity.
  unfold C, SaS, SaR, RaS, RaR; reflexivity.

  
Abort.

(* injective on the right, injective on the left *)
                         