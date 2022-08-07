From Cat Require Export Cat.
From Cat.Limits Require Import InitTerm.

#[refine]
#[export]
Instance SubcatOb (C : Cat) (P : Ob C -> Prop) : Cat :=
{
  Ob := {X : Ob C | P X};
  Hom := fun A B : {X : Ob C | P X} => @Hom C (proj1_sig A) (proj1_sig B);
  HomSetoid := fun A B => @HomSetoid C (proj1_sig A) (proj1_sig B);
  comp := fun X Y Z => @comp C (proj1_sig X) (proj1_sig Y) (proj1_sig Z);
  id := fun X => @id C (proj1_sig X)
}.
Proof. all: cat. Defined.
