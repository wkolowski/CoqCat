From Cat Require Export Cat.
From Cat.Limits Require Export InitTerm.
From Cat.Limits Require Export ProdCoprod.

Set Universe Polymorphism.

Class HasExponentials (C : Cat) {hp : HasProducts C} : Type :=
{
  expOb : Ob C -> Ob C -> Ob C;
  eval : forall {X Y : Ob C}, Hom (prodOb (expOb X Y) X) Y;
  curry : forall {X Y Z : Ob C}, Hom (prodOb Z X) Y -> Hom Z (expOb X Y);
  Proper_curry :> forall X Y Z : Ob C, Proper (equiv ==> equiv) (@curry X Y Z);
  he_comp :
    forall {X Y E : Ob C} (f : Hom (prodOb E X) Y),
      curry f ×' id X .> eval == f;
  he_unique :
    forall {X Y E : Ob C} (f : Hom (prodOb E X) Y) (g : Hom E (expOb X Y)),
      g ×' id X .> eval == f -> g == curry f;
}.

Section Exponential.

Context
  [C : Cat]
  [hp : HasProducts C]
  [he : HasExponentials C]
  [X Y Z : Ob C].

Lemma universal_property :
  forall {E : Ob C} (f : Hom (prodOb E X) Y) (g : Hom E (expOb X Y)),
    curry f == g <-> g ×' id X .> eval == f.
Proof.
  split.
  - intros <-. apply he_comp.
  - intros Heq. symmetry. apply he_unique. assumption.
Qed.

Lemma computation_rule :
  forall f : Hom (prodOb (expOb X Y) X) Y,
    curry f ×' id X .> eval == f.
Proof.
  intros f.
  apply he_comp.
Qed.

Lemma uniqueness_rule :
  forall {E : Ob C} (f : Hom (prodOb E X) Y) (g : Hom E (expOb X Y)),
    g ×' id X .> eval == f -> g == curry f.
Proof.
  intros f.
  apply he_unique.
Qed.

Definition uncurry (f : Hom X (expOb Y Z)) : Hom (prodOb X Y) Z := f ×' (id Y) .> eval.

#[export]
Instance Proper_uncurry : Proper (equiv ==> equiv) uncurry.
Proof.
  intros f g Heq.
  unfold uncurry.
  rewrite Heq.
  reflexivity.
Qed.

Lemma curry_uncurry :
  forall f : Hom X (expOb Y Z),
    curry (uncurry f) == f.
Proof.
  intros f.
  unfold uncurry.
  symmetry.
  apply he_unique.
  reflexivity.
Qed.

End Exponential.

Lemma uncurry_curry :
  forall
    {C : Cat} {hp : HasProducts C} (he : HasExponentials C)
    (X Y Z : Ob C) (f : Hom (prodOb X Y) Z),
      uncurry (curry f) == f.
Proof.
  intros C hp he X Y Z f.
  unfold uncurry.
  apply he_comp.
Qed.

Section Exponential.

Context
  [C : Cat]
  [hp : HasProducts C]
  [he : HasExponentials C]
  [X Y Z : Ob C].

Lemma curry_eval :
  curry eval == id (expOb X Y).
Proof.
  symmetry; apply he_unique.
  unfold ProductFunctor_fmap.
  fpair.
Qed.

Lemma curry_comp :
  forall (A : Ob C) (f : Hom Y Z) (g : Hom Z A),
    curry (eval (X := X) .> f .> g) == curry (eval .> f) .> curry (eval .> g).
Proof.
  intros.
  symmetry; apply he_unique.
  rewrite <- (comp_id_l X), ProductFunctor_fmap_comp, comp_assoc.
  rewrite he_comp, <- comp_assoc, he_comp, comp_assoc.
  reflexivity.
Qed.

Lemma uncurry_id :
  uncurry (id (expOb X Y)) == eval.
Proof.
  unfold uncurry.
  unfold ProductFunctor_fmap.
  fpair.
Qed.

End Exponential.