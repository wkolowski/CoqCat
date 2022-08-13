From Cat Require Export Cat.
From Cat.Limits Require Import Product Coproduct.

Set Implicit Arguments.

Section Traditional.

Definition isBiproduct
  (C : Cat) {A B : Ob C} (P : Ob C)
  (pA : Hom P A) (pB : Hom P B) (iA : Hom A P) (iB : Hom B P)
  (fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P)
  (copair : forall {X : Ob C} (f : Hom A X) (g : Hom B X), Hom P X)
  : Prop := isProduct C P pA pB (@fpair) /\ isCoproduct C P iA iB (@copair).

Lemma isBiproduct_Dual :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y) (q1 : Hom X P) (q2 : Hom Y P)
    (fpair : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P)
    (copair : forall (P' : Ob C) (q1' : Hom X P') (q2' : Hom Y P'), Hom P P'),
      isBiproduct (Dual C) P q1 q2 p1 p2 copair fpair
        <->
      isBiproduct C P p1 p2 q1 q2 fpair copair.
Proof. firstorder. Defined.

End Traditional.

Class HasBiproducts (C : Cat) : Type :=
{
  HasProducts_HasBiproducts :> HasProducts C;
  HasCoproducts_HasBiproducts :> HasCoproducts C;
  isProduct_isCoproduct : forall X Y : Ob C, prodOb X Y = coprodOb X Y
}.

Coercion HasProducts_HasBiproducts : HasBiproducts >-> HasProducts.
Coercion HasCoproducts_HasBiproducts : HasBiproducts >-> HasCoproducts.

#[refine]
#[export]
Instance HasBiproducts_Dual (C : Cat) (hp : HasBiproducts C) : HasBiproducts (Dual C) :=
{
  HasProducts_HasBiproducts := HasProducts_Dual hp;
  HasCoproducts_HasBiproducts := HasCoproducts_Dual hp;
}.
Proof.
  simpl. intros. rewrite isProduct_isCoproduct. trivial.
Defined.

#[refine]
#[export]
Instance BiproductBifunctor {C : Cat} {hp : HasBiproducts C} : Bifunctor C C C :=
{
  biob := @coprodOb C hp;
  bimap :=
    fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') => copair (f .> finl) (g .> finr)
}.
Proof.
  unfold Proper, respectful. all: copair.
Defined.