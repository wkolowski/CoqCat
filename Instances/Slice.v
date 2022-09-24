From Cat Require Import Cat.

Set Implicit Arguments.

Class SliceOb (C : Cat) (Y : Ob C) : Type :=
{
  dom : Ob C;
  mor : Hom dom Y
}.

Arguments dom [C] [Y] _.
Arguments mor [C] [Y] _.

Coercion dom : SliceOb >-> Ob.

Definition SliceHom {C : Cat} {Y : Ob C} (A B : SliceOb C Y) : Type :=
  {f : Hom A B | mor A == f .> mor B}.

#[refine]
#[export]
Instance SliceHomSetoid {C : Cat} {Y : Ob C} (A B : SliceOb C Y) : Setoid (SliceHom A B) :=
{
  equiv := fun f g : SliceHom A B => proj1_sig f == proj1_sig g
}.
Proof. now solve_equiv. Defined.

Definition SliceComp
  {C : Cat} {A : Ob C} (X Y Z : SliceOb C A) (f : SliceHom X Y) (g : SliceHom Y Z) : SliceHom X Z.
Proof.
  destruct f as [f Hf], g as [g Hg]; red.
  exists (f .> g).
  now rewrite comp_assoc, <- Hg.
Defined.

Definition SliceId {C : Cat} {Y : Ob C} (X : SliceOb C Y) : SliceHom X X.
Proof.
  exists (id X).
  now rewrite comp_id_l.
Defined.

#[refine]
#[export]
Instance Slice (C : Cat) (T : Ob C) : Cat :=
{
  Ob := SliceOb C T;
  Hom := @SliceHom C T;
  HomSetoid := @SliceHomSetoid C T;
  comp := @SliceComp C T;
  id := @SliceId C T;
}.
Proof.
  - intros [X x] [Y y] [Z z] [f1 Hf1] [f2 Hf2] Hf [g1 Hg1] [g2 Hg2] Hg; cbn in *.
    now rewrite Hf, Hg.
  - intros [X x] [Y y] [Z z] [W w] [f Hf] [g Hg] [h Hh]; cbn in *.
    now rewrite comp_assoc.
  - intros [X x] [Y y] [f Hf]; cbn in *.
    now rewrite comp_id_l.
  - intros [X x] [Y y] [f Hf]; cbn in *.
    now rewrite comp_id_r.
Defined.