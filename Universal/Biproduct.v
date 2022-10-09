From Cat Require Import Cat.
From Cat.Universal Require Import Product Coproduct.

Set Implicit Arguments.

(**
  See:
  - https://ncatlab.org/nlab/show/biproduct for the old-fashioned definition
  - https://qchu.wordpress.com/2012/09/14/a-meditation-on-semiadditive-categories/
    for some rationale why it was defined like this
  - http://cahierstgdc.com/wp-content/uploads/2020/07/KARVONEN-LXI-3.pdf
    for a better definition that is used in this file
  - https://mathoverflow.net/questions/428546/how-exotic-can-an-infinite-biproduct-in-an-additive-category-be
    for why (infinite) indexed biproducts don't make much sense
*)

Class isBiproduct
  (C : Cat) {A B : Ob C}
  (P : Ob C) (outl : Hom P A) (outr : Hom P B) (finl : Hom A P) (finr : Hom B P)
  (fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P)
  (copair : forall {X : Ob C} (f : Hom A X) (g : Hom B X), Hom P X)
  : Prop :=
{
  isBiproduct_isProduct   :> isProduct C P outl outr (@fpair);
  isBiproduct_isCoproduct :> isCoproduct C P finl finr (@copair);
  isBiproduct_ok : outl .> finl .> outr .> finr == outr .> finr .> outl .> finl;
}.

#[export] Hint Mode isBiproduct ! ! ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isBiproduct ! ! ! - - - - - - - : core.

Class HasBiproducts (C : Cat) : Type :=
{
  HasProducts_HasBiproducts :> HasProducts C;
  HasCoproducts_HasBiproducts :> HasCoproducts C;
  HasBiproducts_spec : product = coproduct;
}.

Coercion HasProducts_HasBiproducts : HasBiproducts >-> HasProducts.
Coercion HasCoproducts_HasBiproducts : HasBiproducts >-> HasCoproducts.

#[export]
Instance BiproductBifunctor {C : Cat} {hp : HasBiproducts C} : Bifunctor C C C :=
  @CoproductBifunctor C hp.

Class HasBiproducts' (C : Cat) : Type :=
{
  biproduct : Ob C -> Ob C -> Ob C;

  bioutl   : forall {A B : Ob C}, Hom (biproduct A B) A;
  bioutr   : forall {A B : Ob C}, Hom (biproduct A B) B;
  bipair  : forall {A B Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ (biproduct A B);
  isProduct_HasBiproducts' :>
    forall {A B : Ob C}, isProduct C (biproduct A B) bioutl bioutr (@bipair A B);

  binl     : forall {A B : Ob C}, Hom A (biproduct A B);
  binr     : forall {A B : Ob C}, Hom B (biproduct A B);
  bicopair : forall {A B : Ob C} {P : Ob C} (f : Hom A P) (g : Hom B P), Hom (biproduct A B) P;

  isCoproduct_HasBiproducts :>
    forall {A B : Ob C}, isCoproduct C (@biproduct A B) binl binr (@bicopair A B);

  HasBiproducts'_ok :
    forall {A B : Ob C},
      @bioutl A B .> @binl A B .> @bioutr A B .> @binr A B
        ==
      bioutr .> binr .> bioutl .> binl;
}.

#[export]
Instance BiproductBifunctor' {C : Cat} {hp : HasBiproducts C} : Bifunctor C C C :=
  @CoproductBifunctor C hp.