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
  - https://mathoverflow.net/questions/428546/
    for why (infinite) indexed biproducts don't make much sense
*)

Class isBiproduct
  (C : Cat) {A B : Ob C}
  (P : Ob C) (outl : Hom P A) (outr : Hom P B) (finl : Hom A P) (finr : Hom B P)
  (fpair  : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P)
  (copair : forall {X : Ob C} (f : Hom A X) (g : Hom B X), Hom P X)
  : Prop :=
{
  isBiproduct_isProduct   :: isProduct C P outl outr (@fpair);
  isBiproduct_isCoproduct :: isCoproduct C P finl finr (@copair);
  isBiproduct_ok : outl .> finl .> outr .> finr == outr .> finr .> outl .> finl;
}.

#[export] Hint Mode isBiproduct ! ! ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isBiproduct ! ! ! - - - - - - - : core.

Class HasBiproducts (C : Cat) : Type :=
{
  HasProducts_HasBiproducts :: HasProducts C;
  HasCoproducts_HasBiproducts :: HasCoproducts C;
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
  isProduct_HasBiproducts' ::
    forall {A B : Ob C}, isProduct C (biproduct A B) bioutl bioutr (@bipair A B);

  binl     : forall {A B : Ob C}, Hom A (biproduct A B);
  binr     : forall {A B : Ob C}, Hom B (biproduct A B);
  bicopair : forall {A B : Ob C} {P : Ob C} (f : Hom A P) (g : Hom B P), Hom (biproduct A B) P;
  isCoproduct_HasBiproducts ::
    forall {A B : Ob C}, isCoproduct C (@biproduct A B) binl binr (@bicopair A B);

  binl_bioutl :
    forall {A B : Ob C},
      @binl A B .> bioutl == id A;
  binr_bioutr :
    forall {A B : Ob C},
      @binr A B .> bioutr == id B;

  HasBiproducts'_ok :
    forall {A B : Ob C},
      @bioutl A B .> @binl A B .> @bioutr A B .> @binr A B
        ==
      bioutr .> binr .> bioutl .> binl;
}.

Definition zero {C : Cat} {hb : HasBiproducts' C} {A B : Ob C} : Hom A B :=
  @binl _ _ A B .> bioutr.

Definition bidiag {C : Cat} {hp : HasBiproducts' C} {A : Ob C} : Hom A (biproduct A A) :=
  bipair (id A) (id A).

Definition bicodiag {C : Cat} {hp : HasBiproducts' C} {A : Ob C} : Hom (biproduct A A) A :=
  bicopair (id A) (id A).

Definition biadd
  {C : Cat} {hb : HasBiproducts' C}
  {A B : Ob C} (f g : Hom A B) : Hom A B :=
    bipair f g .> bicodiag.

Section BiproductIdentities.

Context
  (C : Cat)
  (hb : HasBiproducts' C)
  (A B : Ob C).

Lemma binl_bioutr :
  forall {X : Ob C} (f : Hom B X),
    @binl _ _ A B .> bioutr .> f == @binl _ _ A X .> bioutr.
Proof.
  intros.
  (* assert (
    bioutr .> binr .> bioutl .> @binl _ _ A B .> bioutr .> f
      ==
    bioutr .> binr .> bioutl .> @binl _ _ A X .> bioutr).
  ). *)
Admitted.

Lemma binl_bioutr' :
  forall {X : Ob C} (f : Hom X A),
    f .> @binl _ _ A B .> bioutr == @binl _ _ X B .> bioutr.
Proof.
Admitted.

Lemma binr_bioutl :
  forall {X : Ob C} (f : Hom A X),
    @binr _ _ A B .> bioutl .> f == @binr _ _ X B .> bioutl.
Proof.
Admitted.

Lemma binr_bioutl' :
  forall {X : Ob C} (f : Hom X B),
    f .> @binr _ _ A B .> bioutl == @binr _ _ A X .> bioutl.
Proof.
  intros.
  assert (H1 : isConstant (@binr _ _ A B .> bioutl)) by admit.
  assert (H2 : isCoconstant (@binr _ _ A B .> bioutl)) by admit.
  unfold isConstant, isCoconstant in H1, H2.
Admitted.

End BiproductIdentities.

Section MoreBiproductIdentities.

Context
  (C : Cat)
  (hb : HasBiproducts' C)
  (A B : Ob C).

Lemma binl_bipair :
  forall {A' B' : Ob C} (f : Hom A A') (g : Hom B B'),
    binl .> bipair (bioutl .> f) (bioutr .> g) == f .> binl.
Proof.
  intros.
  rewrite equiv_product', !comp_assoc, fpair_outl, fpair_outr.
  rewrite binl_bioutl, <- !comp_assoc, binl_bioutl, comp_id_l, comp_id_r.
  now rewrite binl_bioutr, binl_bioutr'.
Qed.

Lemma binr_bipair :
  forall {A' B' : Ob C} (f : Hom A A') (g : Hom B B'),
    binr .> bipair (bioutl .> f) (bioutr .> g) == g .> binr.
Proof.
  intros.
  rewrite equiv_product', !comp_assoc, fpair_outl, fpair_outr.
  rewrite binr_bioutr, <- !comp_assoc, binr_bioutr, comp_id_l, comp_id_r.
  now rewrite binr_bioutl, binr_bioutl'.
Qed.

Lemma bicopair_bioutl :
  forall {A' B' : Ob C} (f : Hom A A') (g : Hom B B'),
    bicopair (f .> binl) (g .> binr) .> bioutl == bioutl .> f.
Proof.
  intros.
  rewrite equiv_coproduct', <- !comp_assoc, finl_copair, finr_copair.
  rewrite binr_bioutl, binr_bioutl'.
  now rewrite binl_bioutl, comp_assoc, binl_bioutl, comp_id_l, comp_id_r.
Defined.

Lemma bicopair_bioutr :
  forall {A' B' : Ob C} (f : Hom A A') (g : Hom B B'),
    bicopair (f .> binl) (g .> binr) .> bioutr == bioutr .> g.
Proof.
  intros.
  rewrite equiv_coproduct', <- !comp_assoc, finl_copair, finr_copair.
  rewrite binl_bioutr, binl_bioutr'.
  now rewrite binr_bioutr, comp_assoc, binr_bioutr, comp_id_l, comp_id_r.
Defined.

End MoreBiproductIdentities.

#[refine]
#[export]
Instance BiproductBifunctor' {C : Cat} {hp : HasBiproducts' C} : Bifunctor C C C :=
{
  biob := fun X Y : Ob C => biproduct X Y;
  bimap :=
    fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') =>
      bicopair (f .> binl) (g .> binr);
}.
Proof.
  - now proper.
  - now intros; rewrite equiv_coproduct', copair_comp, !comp_assoc, !finl_copair, !finr_copair.
  - now intros; rewrite equiv_coproduct', finl_copair, finr_copair, !comp_id_l, !comp_id_r.
Defined.

Notation "A ×+ B" := (@biob _ _ _ (@BiproductBifunctor' _ _) A B) (at level 40, only parsing).
Notation "f ×+' g" := (@bimap _ _ _ (@BiproductBifunctor' _ _) _ _ _ _ f g) (at level 40).
