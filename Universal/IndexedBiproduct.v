From Cat Require Import Cat.
From Cat.Universal Require Import IndexedProduct IndexedCoproduct.

Class isIndexedBiproduct
  (C : Cat) {J : Set} {A : J -> Ob C} (P : Ob C)
  (proj : forall j : J, Hom P (A j)) (coproj : forall j : J, Hom (A j) P)
  (tuple : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P)
  (cotuple : forall (X : Ob C) (f : forall j : J, Hom (A j) X), Hom P X)
  : Prop :=
{
  isIndexedProduct_isIndexedBiproduct :> isIndexedProduct C P proj tuple;
  isIndexedCoproduct_isIndexedBiproduct :> isIndexedCoproduct C P coproj cotuple;
}.

Class HasIndexedBiproducts (C : Cat) : Type :=
{
  indexedBiproduct : forall {J : Set} (A : J -> Ob C), Ob C;
  HasIndexedProducts'_HasIndexedBiproducts :> HasIndexedProducts' C (@indexedBiproduct);
  HasIndexedCoproducts'_HasIndexedBiproducts :> HasIndexedCoproducts' C (@indexedBiproduct);
}.

(* Coercion HasIndexedProducts_HasIndexedBiproducts : HasIndexedBiproducts >-> HasIndexedProducts. *)
(* Coercion HasIndexedCoproducts_HasIndexedBiproducts : HasIndexedBiproducts >-> HasIndexedCoproducts. *)

(*
#[refine]
#[export]
Instance HasIndexedBiproducts_Dual
  (C : Cat) (hp : HasIndexedBiproducts C) : HasIndexedBiproducts (Dual C) :=
{
  HasIndexedProducts_HasIndexedBiproducts := HasIndexedProducts_Dual C hp;
  HasIndexedCoproducts_HasIndexedBiproducts := HasIndexedCoproducts_Dual C hp;
}.
Proof.
  now cbn; intros; rewrite isProduct_isCoproduct.
Defined.
*)