Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Print product.

Print has_products.

Definition exponential (C : Cat) {hp : has_products C}
  (X Y E : Ob C) (eval : Hom (prodOb E X) Y) : Prop :=
    forall (Z : Ob C) (e : Hom (prodOb Z X) Y),
      exists!! u : Hom Z E, ProductFunctor_fmap u (id X) .> eval == e.

Theorem exponential_unique :
    forall (C : Cat) (hp : has_products C) (X Y : Ob C)
    (E : Ob C) (eval : Hom (prodOb E X) Y)
    (E' : Ob C) (eval' : Hom (prodOb E' X) Y),
        exponential C X Y E eval -> exponential C X Y E' eval' -> E ~ E'.
Proof.
  intros. red in H, H0.
  destruct (H0 E eval) as [u [Hu1 Hu2]], (H E' eval') as [u' [Hu'1 Hu'2]].
  exists u, u'. split.
    rewrite <- Hu1, <- comp_assoc in Hu'1.
      rewrite <- ProductFunctor_fmap_pres_comp in Hu'1.
      rewrite id_left in Hu'1.