From Cat Require Import Cat.
From Cat.Universal Require Import IndexedProduct IndexedCoproduct.

Class isIndexedBiproduct
  (C : Cat) {J : Type} {A : J -> Ob C}
  (P : Ob C) (out : forall j : J, Hom P (A j)) (inj : forall j : J, Hom (A j) P)
  (tuple : forall {X : Ob C} (f : forall j : J, Hom X (A j)), Hom X P)
  (cotuple : forall {X : Ob C} (f : forall j : J, Hom (A j) X), Hom P X)
  : Prop :=
{
  isIndexedProduct_isIndexedBiproduct :> isIndexedProduct C P out (@tuple);
  isIndexedCoproduct_isIndexedBiproduct :> isIndexedCoproduct C P inj (@cotuple);
}.

#[export] Hint Mode isIndexedBiproduct ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isIndexedBiproduct ! ! ! - - - - - : core.

Class HasIndexedBiproducts (C : Cat) : Type :=
{
  HasIndexedProducts_HasIndexedBiproducts :> HasIndexedProducts C;
  HasIndexedCoproducts_HasIndexedBiproducts :> HasIndexedCoproducts C;
  HasIndexedBiproducts_spec : @indexedProduct C _ = @indexedCoproduct C _;
}.

Coercion HasIndexedProducts_HasIndexedBiproducts
  : HasIndexedBiproducts >-> HasIndexedProducts.

Coercion HasIndexedCoproducts_HasIndexedBiproducts
  : HasIndexedBiproducts >-> HasIndexedCoproducts.