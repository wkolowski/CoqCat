From Cat Require Export Cat.
From Cat.Universal Require Import Product Coproduct.

Set Implicit Arguments.

Class isBiproduct
  (C : Cat) {A B : Ob C}
  (P : Ob C) (outl : Hom P A) (outr : Hom P B) (finl : Hom A P) (finr : Hom B P)
  (fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P)
  (copair : forall {X : Ob C} (f : Hom A X) (g : Hom B X), Hom P X)
  : Prop :=
{
  isBiproduct_isProduct   :> isProduct C P outl outr (@fpair);
  isBiproduct_isCoproduct :> isCoproduct C P finl finr (@copair);
}.

#[export] Hint Mode isBiproduct ! ! ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isBiproduct ! ! ! - - - - - - - : core.

Lemma isBiproduct_Dual :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (outl : Hom P X) (outr : Hom P Y) (finl : Hom X P) (finr : Hom Y P)
    (fpair : forall (P' : Ob C) (outl' : Hom P' X) (outr' : Hom P' Y), Hom P' P)
    (copair : forall (P' : Ob C) (finl' : Hom X P') (finr' : Hom Y P'), Hom P P'),
      isBiproduct (Dual C) P finl finr outl outr copair fpair
        <->
      isBiproduct C P outl outr finl finr fpair copair.
Proof. firstorder. Qed.

(* Class HasBiproducts (C : Cat) : Type :=
{
  biproduct : Ob C -> Ob C -> Ob C;
  HasProducts'_HasBiproducts :> HasProducts' C biproduct;
  HasCoproducts'_HasBiproducts :> HasCoproducts' C biproduct;
}.

Coercion HasProducts'_HasBiproducts : HasBiproducts >-> HasProducts'.
Coercion HasCoproducts'_HasBiproducts : HasBiproducts >-> HasCoproducts'.

#[export]
Instance HasProducts_HasBiproducts {C : Cat} (hb : HasBiproducts C) : HasProducts C :=
{
  product := biproduct;
}.

#[export]
Instance HasCoproducts_HasBiproducts {C : Cat} (hb : HasBiproducts C) : HasCoproducts C :=
{
  coproduct := biproduct;
}.

Coercion HasProducts_HasBiproducts : HasBiproducts >-> HasProducts.
Coercion HasCoproducts_HasBiproducts : HasBiproducts >-> HasCoproducts. *)

Class HasBiproducts (C : Cat) : Type :=
{
  HasProducts_HasBiproducts :> HasProducts C;
  HasCoproducts_HasBiproducts :> HasCoproducts C;
  HasBiproducts_spec : product = coproduct;
}.

Coercion HasProducts_HasBiproducts : HasBiproducts >-> HasProducts.
Coercion HasCoproducts_HasBiproducts : HasBiproducts >-> HasCoproducts.

#[refine]
#[export]
Instance BiproductBifunctor {C : Cat} {hp : HasBiproducts C} : Bifunctor C C C :=
{
  biob := @coproduct C hp;
  bimap :=
    fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') => copair (f .> finl) (g .> finr)
}.
Proof.
  all: solve_coproduct.
Defined.