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
Proof. solve_equiv. Defined.

Definition SliceComp
  {C : Cat} {A : Ob C} (X Y Z : SliceOb C A) (f : SliceHom X Y) (g : SliceHom Y Z) : SliceHom X Z.
Proof.
  destruct f as [f Hf], g as [g Hg]; red.
  exists (f .> g).
  rewrite comp_assoc. rewrite <- Hg. assumption.
Defined.

Definition SliceId {C : Cat} {Y : Ob C} (X : SliceOb C Y) : SliceHom X X.
Proof.
  red. exists (id X).
  now rewrite comp_id_l.
Defined.

#[refine]
#[export]
Instance Slice (C : Cat) (Y : Ob C) : Cat :=
{
  Ob := SliceOb C Y;
  Hom := @SliceHom C Y;
  HomSetoid := @SliceHomSetoid C Y;
  comp := @SliceComp C Y;
  id := @SliceId C Y
}.
Proof.
  unfold Proper, respectful; intros.
  1: now destruct x, y, x0, y0; cbn in *; rewrite H, H0.
  all: (cat; repeat
  match goal with
  | f : SliceHom _ _ |- _ => destruct f; cbn in *
  end; cat).
Defined.