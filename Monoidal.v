Require Import Cat.Cat.
Require Import Cat.Bifunctor.

Require Import Limits.InitTerm.
Require Import Limits.BinProdCoprod.

Require Import CartesianClosed.

Set Implicit Arguments.

Class Monoidal : Type :=
{
    cat : Cat;
    tensor : Bifunctor cat cat cat;
    tensor_unit : Ob cat;
    associator : forall X Y Z : Ob cat,
      Hom (biob (biob X Y) Z) (biob X (biob Y Z));
    associator_iso : forall X Y Z : Ob cat,
      Iso (associator X Y Z);
    left_unitor : forall X : Ob cat, Hom (biob tensor_unit X) X;        
    left_unitor_iso : forall X : Ob cat, Iso (left_unitor X);
    right_unitor : forall X : Ob cat, Hom (biob X tensor_unit) X;
    right_unitor_iso : forall X : Ob cat, Iso (right_unitor X);
    triangle : forall X Y : Ob cat,
      associator X tensor_unit Y .> bimap (id X) (left_unitor Y) ==
      bimap (right_unitor X) (id Y);
    pentagon : forall W X Y Z : Ob cat,
      bimap (associator W X Y) (id Z) .> associator W (biob X Y) Z .>
        bimap (id W) (associator X Y Z) ==
      associator (biob W X) Y Z .> associator W X (biob Y Z)
}.

Coercion cat : Monoidal >-> Cat.

#[refine]
Instance Monoidal_has_terminal_and_products
  (C : Cat) (ht : has_term C) (hp : has_products C) : Monoidal :=
{
    cat := C;
    tensor := @ProductBifunctor C hp;
    tensor_unit := @term C ht;
}.
Proof.
  all: cbn; intros.
  exact (proj1_sig (prodOb_assoc' hp X Y Z)).
  exact (proj2_sig (prodOb_assoc' hp X Y Z)).
  exact (proj1_sig (prod_term_iso_l' C X ht hp)).
  exact (proj2_sig (prod_term_iso_l' C X ht hp)).
  exact (proj1_sig (prod_term_iso_r' C X ht hp)).
  exact (proj2_sig (prod_term_iso_r' C X ht hp)).
  cbn. fpair.
  cbn. fpair.
Defined.

#[refine]
Instance Monoidal_has_initial_and_coproducts
  (C : Cat) (hi : has_init C) (hp : has_coproducts C) : Monoidal :=
{
    cat := C;
    tensor := @CoproductBifunctor C hp;
    tensor_unit := @init C hi;
}.
Proof.
  all: cbn; intros.
  exact (proj1_sig (coprodOb_assoc' hp X Y Z)).
  exact (proj2_sig (coprodOb_assoc' hp X Y Z)).
  exact (proj1_sig (coprod_init_iso_l' C X hi hp)).
  exact (proj2_sig (coprod_init_iso_l' C X hi hp)).
  exact (proj1_sig (coprod_init_iso_r' C X hi hp)).
  exact (proj2_sig (coprod_init_iso_r' C X hi hp)).
  cbn. copair. init.
  cbn. copair.
Defined.