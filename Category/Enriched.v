From Cat Require Import Cat.
From Cat.Category Require Import CartesianClosed Monoidal.
From Cat.Limits Require Import InitTerm ProdCoprod.
From Cat Require Import Instances.Setoids.

Class Enriched (V : Monoidal) : Type :=
{
  EOb : Type;
  EHom : EOb -> EOb -> Ob V;
  EComp : forall X Y Z : EOb, Hom (@biob V V V tensor (EHom X Y) (EHom Y Z)) (EHom X Z);
  EId : forall X : EOb, Hom tensor_unit (EHom X X);
  EComp_assoc :
    forall A B C D : EOb,
      associator (EHom A B) (EHom B C) (EHom C D) .>
        bimap (id (EHom A B)) (EComp B C D) .> EComp A B D
          ==
        bimap (EComp A B C) (id (EHom C D)) .> EComp A C D;
  EComp_unital_left :
    forall A B : EOb, bimap (EId A) (id (EHom A B)) .> EComp A A B == left_unitor (EHom A B);
  EComp_unital_right :
    forall A B : EOb, bimap (id (EHom A B)) (EId B) .> EComp A B B == right_unitor (EHom A B);
}.

#[export]
Instance wut (C : Cat) (X Y : Ob C) : Setoid' :=
{
  carrier := @Hom C X Y;
  setoid := @HomSetoid C X Y;
}.

#[refine]
#[export]
Instance Enriched_CoqSetoid
  : Enriched (Monoidal_HasTerminal_and_products CoqSetoid_HasTerm CoqSetoid_HasProducts)
  := {}.
Proof.
  exact (Ob CoqSetoid).
  intros X Y. exact (wut _ X Y).
  cbn. intros.
    split with (fun p => SetoidComp (fst p) (snd p)). proper.
      destruct H, x, y. cbn in *. rewrite H, H0. reflexivity.
  intros. cbn. exists (fun _ => id X). proper.
  cbn. reflexivity.
  cbn. reflexivity.
  cbn. reflexivity.
Defined.