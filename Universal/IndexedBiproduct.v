From Cat Require Import Cat.
From Cat.Universal Require Import IndexedProduct IndexedCoproduct.

Class isIndexedBiproduct
  (C : Cat) {J : Set} {A : J -> Ob C}
  (P : Ob C) (proj : forall j : J, Hom P (A j)) (coproj : forall j : J, Hom (A j) P)
  (tuple : forall {X : Ob C} (f : forall j : J, Hom X (A j)), Hom X P)
  (cotuple : forall {X : Ob C} (f : forall j : J, Hom (A j) X), Hom P X)
  : Prop :=
{
  isIndexedProduct_isIndexedBiproduct :> isIndexedProduct C P proj (@tuple);
  isIndexedCoproduct_isIndexedBiproduct :> isIndexedCoproduct C P coproj (@cotuple);
}.

#[export] Hint Mode isIndexedBiproduct ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isIndexedBiproduct ! ! ! - - - - - : core.

(* Class HasIndexedBiproducts (C : Cat) : Type :=
{
  indexedBiproduct : forall {J : Set} (A : J -> Ob C), Ob C;
  HasIndexedProducts'_HasIndexedBiproducts :> HasIndexedProducts' C (@indexedBiproduct);
  HasIndexedCoproducts'_HasIndexedBiproducts :> HasIndexedCoproducts' C (@indexedBiproduct);
}.

Coercion HasIndexedProducts'_HasIndexedBiproducts
  : HasIndexedBiproducts >-> HasIndexedProducts'.

Coercion HasIndexedCoproducts'_HasIndexedBiproducts
  : HasIndexedBiproducts >-> HasIndexedCoproducts'. *)

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