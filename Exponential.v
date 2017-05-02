Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Print product.

Print has_products.

Definition exponential {C : Cat} {hp : has_products C}
  (X Y E : Ob C) (eval : Hom (prodOb E X) Y) : Prop :=
    forall (Z : Ob C) (e : Hom (prodOb Z X) Y),
      exists!! u : Hom Z E, ProductFunctor_fmap u (id X) .> eval == e.

Theorem exponential_unique :
    forall (C : Cat) (hp : has_products C) (X Y : Ob C)
    (E : Ob C) (eval : Hom (prodOb E X) Y)
    (E' : Ob C) (eval' : Hom (prodOb E' X) Y),
        exponential X Y E eval -> exponential X Y E' eval' -> E ~ E'.
Proof.
  intros. red in H, H0.
  destruct (H0 E eval) as [u [Hu1 Hu2]], (H E' eval') as [u' [Hu'1 Hu'2]].
  exists u, u'. split.
    destruct (H E eval) as [f [Hf1 Hf2]].
    assert (f == id E).
      apply Hf2. rewrite ProductFunctor_fmap_pres_id, id_left. reflexivity.
      rewrite <- H1. symmetry. apply Hf2.
        rewrite <- Hu'1, <- comp_assoc,
        <- ProductFunctor_fmap_pres_comp in Hu1.
        assert (ProductFunctor_fmap (u .> u') (id X .> id X)
          == ProductFunctor_fmap (u .> u') (id X)).
          apply ProductFunctor_fmap_Proper; auto. exact (id X). reflexivity.
          rewrite H2 in Hu1. assumption.
    destruct (H0 E' eval') as [f [Hf1 Hf2]].
    assert (f == id E').
      apply Hf2. rewrite ProductFunctor_fmap_pres_id, id_left. reflexivity.
      rewrite <- H1. symmetry. apply Hf2.
        rewrite <- Hu1, <- comp_assoc,
        <- ProductFunctor_fmap_pres_comp in Hu'1.
        assert (ProductFunctor_fmap (u' .> u) (id X .> id X)
          == ProductFunctor_fmap (u' .> u) (id X)).
          apply ProductFunctor_fmap_Proper; auto. exact (id X). reflexivity.
          rewrite H2 in Hu'1. assumption.
Defined.

Class has_exponentials (C : Cat) {hp : has_products C} : Type :=
{
    expOb : Ob C -> Ob C -> Ob C;
    eval : forall X Y : Ob C,
      Hom (prodOb (expOb X Y) X) Y;
    is_exponential : forall (X Y : Ob C),
      exponential X Y (expOb X Y) (eval X Y)
}.