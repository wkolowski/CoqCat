Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Cat.Cat.
Require Import Cat.Bifunctor.

Require Import Limits.InitTerm.
Require Import Limits.BinProdCoprod.

Require Import CartesianClosed.

Require Import Monoidal.

Class Enriched (V : Monoidal) : Type :=
{
    EOb : Type;
    EHom : EOb -> EOb -> Ob V;
    EComp : forall X Y Z : EOb,
      Hom (@biob V V V tensor (EHom X Y) (EHom Y Z)) (EHom X Z);
    EId : forall X : EOb, Hom tensor_unit (EHom X X);
    EComp_assoc : forall A B C D : EOb,
      associator (EHom A B) (EHom B C) (EHom C D) .>
        bimap (id (EHom A B)) (EComp B C D) .> EComp A B D ==
      bimap (EComp A B C) (id (EHom C D)) .> EComp A C D;
    EComp_unital_left : forall A B : EOb,
      bimap (EId A) (id (EHom A B)) .> EComp A A B ==
      left_unitor (EHom A B);
    EComp_unital_right : forall A B : EOb,
      bimap (id (EHom A B)) (EId B) .> EComp A B B ==
      right_unitor (EHom A B);
}.

Check Monoidal_has_terminal_and_products.
Require Import Instances.Setoids.
Instance Enriched_CoqSetoid : Enriched
  (Monoidal_has_terminal_and_products
    CoqSetoid
    CoqSetoid_has_term
    CoqSetoid_has_products) := {}.
Proof.
  exact (Ob CoqSetoid).
  cbn. Search Setoid'.
  intros. cbn. change Setoid' with (Ob CoqSetoid). apply (@Hom CoqSetoid). 





