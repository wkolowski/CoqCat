From Cat Require Import Cat.
From Cat.Limits Require Import InitTerm Coproduct IndexedProduct IndexedCoproduct.

Section Traditional.

Definition isIndexedBiproduct
  (C : Cat) {J : Set} {A : J -> Ob C} (P : Ob C)
  (proj : forall j : J, Hom P (A j)) (coproj : forall j : J, Hom (A j) P)
  (diag : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P)
  (codiag : forall (X : Ob C) (f : forall j : J, Hom (A j) X), Hom P X)
  : Prop :=
    isIndexedProduct C P proj diag /\ isIndexedCoproduct C P coproj codiag.

End Traditional.

Class HasIndexedBiproducts (C : Cat) : Type :=
{
  indexedProduct :> HasIndexedProducts C;
  indexedCoproduct :> HasIndexedCoproducts C;
  isProduct_isCoproduct :
    forall (J : Set) (A : J -> Ob C),
      @indexedProdOb C indexedProduct J A = @indexedCoprodOb C indexedCoproduct J A
}.

Coercion indexedProduct : HasIndexedBiproducts >-> HasIndexedProducts.
Coercion indexedCoproduct : HasIndexedBiproducts >-> HasIndexedCoproducts.

#[refine]
#[export]
Instance HasIndexedBiproducts_Dual
  (C : Cat) (hp : HasIndexedBiproducts C) : HasIndexedBiproducts (Dual C) :=
{
  indexedProduct := HasIndexedProducts_Dual C hp;
  indexedCoproduct := HasIndexedCoproducts_Dual C hp;
}.
Proof.
  intros. simpl. rewrite isProduct_isCoproduct. trivial.
Defined.