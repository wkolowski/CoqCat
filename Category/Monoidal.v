From Cat Require Import Cat.
From Cat.Category Require Import CartesianClosed.
From Cat.Limits Require Import InitTerm ProdCoprod.

Set Implicit Arguments.

Class Monoidal : Type :=
{
  cat : Cat;
  tensor : Bifunctor cat cat cat;
  tensor_unit : Ob cat;
  associator : forall X Y Z : Ob cat, Hom (biob (biob X Y) Z) (biob X (biob Y Z));
  isIso_associator : forall X Y Z : Ob cat, isIso (associator X Y Z);
  left_unitor : forall X : Ob cat, Hom (biob tensor_unit X) X;
  isIso_left_unitor : forall X : Ob cat, isIso (left_unitor X);
  right_unitor : forall X : Ob cat, Hom (biob X tensor_unit) X;
  isIso_right_unitor : forall X : Ob cat, isIso (right_unitor X);
  triangle :
    forall {X Y : Ob cat},
      associator X tensor_unit Y .> bimap (id X) (left_unitor Y) == bimap (right_unitor X) (id Y);
  pentagon :
    forall {W X Y Z : Ob cat},
      bimap (associator W X Y) (id Z) .> associator W (biob X Y) Z .>
        bimap (id W) (associator X Y Z) == associator (biob W X) Y Z .> associator W X (biob Y Z)
}.

Coercion cat : Monoidal >-> Cat.

#[refine]
#[export]
Instance Monoidal_HasTerm_HasProducts
  (C : Cat) (ht : HasTerm C) (hp : HasProducts C) : Monoidal :=
{
  cat := C;
  tensor := @ProductBifunctor C hp;
  tensor_unit := @term C ht;
}.
Proof.
  all: cbn; intros.
  exact (proj1_sig (prodOb_assoc' hp X Y Z)).
  exact (proj2_sig (prodOb_assoc' hp X Y Z)).
  exact (proj1_sig (prodOb_term_l' C ht hp X)).
  exact (proj2_sig (prodOb_term_l' C ht hp X)).
  exact (proj1_sig (prodOb_term_r' C X ht hp)).
  exact (proj2_sig (prodOb_term_r' C X ht hp)).
  cbn. fpair.
  cbn. fpair.
Defined.

#[refine]
#[export]
Instance Monoidal_HasInit_HasCoproducts
  (C : Cat) (hi : HasInit C) (hp : HasCoproducts C) : Monoidal :=
{
  cat := C;
  tensor := @CoproductBifunctor C hp;
  tensor_unit := @init C hi;
}.
Proof.
  all: cbn; intros.
  exact (proj1_sig (coprodOb_assoc' hp X Y Z)).
  exact (proj2_sig (coprodOb_assoc' hp X Y Z)).
  exact (proj1_sig (coprodOb_init_l' C hi hp X)).
  exact (proj2_sig (coprodOb_init_l' C hi hp X)).
  exact (proj1_sig (coprodOb_init_r' C hi hp X)).
  exact (proj2_sig (coprodOb_init_r' C hi hp X)).
  cbn. copair. init.
  cbn. copair.
Defined.