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
  universal :
    forall {X Y E : Ob C} (f : Hom (prodOb E X) Y) (g : Hom E (expOb X Y)),
      curry f == g <-> g ×' id X .> eval == f
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
  intros.
  apply universal.
Qed.

Lemma computation_rule :
  forall f : Hom (prodOb (expOb X Y) X) Y,
    curry f ×' id X .> eval == f.
Proof.
  intros f.
  rewrite <- universal.
  reflexivity.
Qed.

Lemma uniqueness_rule :
  forall {E : Ob C} (f : Hom (prodOb E X) Y) (g : Hom E (expOb X Y)),
    g ×' id X .> eval == f -> g == curry f.
Proof.
  intros.
  symmetry.
  rewrite universal.
  assumption.
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
  rewrite universal.
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
  rewrite <- universal.
  reflexivity.
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
  rewrite universal.
  unfold ProductFunctor_fmap.
  fpair.
Qed.

Lemma curry_comp :
  forall (A : Ob C) (f : Hom Y Z) (g : Hom Z A),
    curry (eval (X := X) .> f .> g) == curry (eval .> f) .> curry (eval .> g).
Proof.
  intros A f g.
  rewrite universal.
  rewrite <- (comp_id_l X), ProductFunctor_fmap_comp, comp_assoc.
  setoid_replace (curry (eval .> g) ×' id X .> eval) with (eval (X := X) .> g)
    by (rewrite <- universal; reflexivity).
  rewrite <- comp_assoc.
  setoid_replace (curry (eval .> f) ×' id X .> eval) with (eval (X := X) .> f)
    by (rewrite <- universal; reflexivity).
  rewrite comp_assoc.
  reflexivity.
Qed.

Lemma uncurry_id :
  uncurry (id (expOb X Y)) == eval.
Proof.
  unfold uncurry.
  rewrite <- universal, curry_eval.
  reflexivity.
Qed.

End Exponential.