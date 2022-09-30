From Cat Require Import Cat.
From Cat.Category Require Import CartesianClosed.
From Cat.Universal Require Import Initial Terminal Product Coproduct.

Set Implicit Arguments.

Class Monoidal : Type :=
{
  cat :> Cat;
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
  - exact Product.associator.
  - exact Product.isIso_associator.
  - exact (proj1_sig (product_term_l' C ht hp X)).
  - exact (proj2_sig (product_term_l' C ht hp X)).
  - exact (proj1_sig (product_term_r' C X ht hp)).
  - exact (proj2_sig (product_term_r' C X ht hp)).
  - cbn; unfold Product.associator; solve_product.
  - cbn; unfold Product.associator; solve_product.
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
  - exact Coproduct.associator.
  - exact Coproduct.isIso_associator.
  - exact (proj1_sig (coproduct_init_l' C hi hp X)).
  - exact (proj2_sig (coproduct_init_l' C hi hp X)).
  - exact (proj1_sig (coproduct_init_r' C hi hp X)).
  - exact (proj2_sig (coproduct_init_r' C hi hp X)).
  - cbn; unfold Coproduct.associator; solve_coproduct; apply equiv_initial.
  - cbn; unfold Coproduct.associator; solve_coproduct.
Defined.