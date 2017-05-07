Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Definition exponential {C : Cat} {hp : has_products C}
  (X Y E : Ob C) (eval : Hom (prodOb E X) Y) : Prop :=
    forall (Z : Ob C) (e : Hom (prodOb Z X) Y),
      exists!! u : Hom Z E, ProductFunctor_fmap u (id X) .> eval == e.

Definition exponential_skolem {C : Cat} {hp : has_products C}
  (X Y E : Ob C) (eval : Hom (prodOb E X) Y)
  (curry : forall E' : Ob C, Hom (prodOb E' X) Y -> Hom E' E) : Prop :=
    forall (E' : Ob C) (eval' : Hom (prodOb E' X) Y),
      setoid_unique (fun u : Hom E' E =>
        ProductFunctor_fmap u (id X) .> eval == eval') (curry E' eval').

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

Theorem exponential_skolem_unique_long :
    forall (C : Cat) (hp : has_products C) (X Y : Ob C)
    (E : Ob C) (eval : Hom (prodOb E X) Y)
      (curry : forall Z : Ob C, Hom (prodOb Z X) Y -> Hom Z E)
    (E' : Ob C) (eval' : Hom (prodOb E' X) Y)
      (curry' : forall Z : Ob C, Hom (prodOb Z X) Y -> Hom Z E'),
        exponential_skolem X Y E eval curry ->
        exponential_skolem X Y E' eval' curry'
        -> E ~ E'.
Proof.
  intros. red. do 2 red in H. do 2 red in H0.
  exists (curry' E eval). red. exists (curry E' eval').
  split.
    destruct (H E eval) as [H1 H2].
      rewrite <- (H2 (curry' E eval .> curry E' eval')).
        rewrite (H2 (id E)).
          reflexivity.
          rewrite ProductFunctor_fmap_pres_id, id_left. reflexivity.
        rewrite ProductFunctor_fmap_pres_comp_l.
          destruct (H E' eval'), (H0 E eval).
            rewrite comp_assoc. rewrite H3. rewrite H5. reflexivity.
    destruct (H0 E' eval') as [H1 H2].
      rewrite <- (H2 (curry E' eval' .> curry' E eval)).
        rewrite (H2 (id E')).
          reflexivity.
          rewrite ProductFunctor_fmap_pres_id, id_left. reflexivity.
        rewrite ProductFunctor_fmap_pres_comp_l.
          destruct (H E' eval'), (H0 E eval).
            rewrite comp_assoc. rewrite H5. rewrite H3. reflexivity.
Qed.

Class has_exponentials (C : Cat) {hp : has_products C} : Type :=
{
    expOb : Ob C -> Ob C -> Ob C;
    eval : forall X Y : Ob C,
      Hom (prodOb (expOb X Y) X) Y;
    curry : forall {X Y Z : Ob C},
      Hom (prodOb Z X) Y -> Hom Z (expOb X Y);
    is_exponential : forall (X Y : Ob C),
      exponential_skolem X Y (expOb X Y) (eval X Y) (@curry X Y)
}.

Arguments expOb [C] [hp] [has_exponentials] _ _.
Arguments eval [C] [hp] [has_exponentials] [X] [Y].
Arguments curry [C] [hp] [has_exponentials] [X] [Y] [Z] _.
Print ProductFunctor.
Arguments ProductFunctor [C] [hp].

Notation "f ×' g" := (ProductFunctor_fmap f g) (at level 40).

Definition uncurry
    {C : Cat} {hp : has_products C} {he : has_exponentials C}
    {X Y Z : Ob C} (f : Hom Z (expOb X Y)) : Hom (prodOb Z X) Y
    := f ×' (id X) .> eval.