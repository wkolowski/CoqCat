From Cat Require Export Cat.
From Cat.Limits Require Export Initial Terminal Product Coproduct.

Definition isExponential
  {C : Cat} {hp : HasProducts C}
  (X Y E : Ob C) (eval : Hom (prodOb E X) Y)
  (curry : forall E' : Ob C, Hom (prodOb E' X) Y -> Hom E' E)
  : Prop :=
    forall (E' : Ob C) (eval' : Hom (prodOb E' X) Y),
      setoid_unique (fun u : Hom E' E =>
        ProductFunctor_fmap u (id X) .> eval == eval') (curry E' eval').

Lemma isExponential_uiso :
  forall
    (C : Cat) (hp : HasProducts C) (X Y : Ob C)
    (E : Ob C) (eval : Hom (prodOb E X) Y)
    (curry : forall Z : Ob C, Hom (prodOb Z X) Y -> Hom Z E)
    (E' : Ob C) (eval' : Hom (prodOb E' X) Y)
    (curry' : forall Z : Ob C, Hom (prodOb Z X) Y -> Hom Z E'),
      isExponential X Y E eval curry ->
      isExponential X Y E' eval' curry' ->
        exists !! f : Hom E E', isIso f /\ f ×' id X .> eval' == eval.
Proof.
  intros. do 2 red in H. do 2 red in H0.
  exists (curry' E eval). repeat split.
    red. exists (curry E' eval').
    split.
      destruct (H E eval) as [H1 H2].
        rewrite <- (H2 (curry' E eval .> curry E' eval')).
          rewrite (H2 (id E)).
            reflexivity.
            rewrite ProductFunctor_fmap_id, comp_id_l. reflexivity.
          rewrite ProductFunctor_fmap_comp_l.
            destruct (H E' eval'), (H0 E eval).
              rewrite comp_assoc. rewrite H3. rewrite H5. reflexivity.
      destruct (H0 E' eval') as [H1 H2].
        rewrite <- (H2 (curry E' eval' .> curry' E eval)).
          rewrite (H2 (id E')).
            reflexivity.
            rewrite ProductFunctor_fmap_id, comp_id_l. reflexivity.
          rewrite ProductFunctor_fmap_comp_l.
            destruct (H E' eval'), (H0 E eval).
              rewrite comp_assoc. rewrite H5. rewrite H3. reflexivity.
    intros. edestruct H0. apply H1.
    intros. edestruct H0. apply H3. rewrite <- H2. apply Proper_comp; cat.
      apply Proper_ProductFunctor_fmap; cat. rewrite H3; cat.
Qed.

Arguments isExponential_uiso {C hp X Y E eval curry E' eval' curry'} _ _.

Lemma isExponential_iso :
  forall
    (C : Cat) (hp : HasProducts C) (X Y : Ob C)
    (E : Ob C) (eval : Hom (prodOb E X) Y)
    (curry : forall Z : Ob C, Hom (prodOb Z X) Y -> Hom Z E)
    (E' : Ob C) (eval' : Hom (prodOb E' X) Y)
    (curry' : forall Z : Ob C, Hom (prodOb Z X) Y -> Hom Z E'),
      isExponential X Y E eval curry -> isExponential X Y E' eval' curry' -> E ~ E'.
Proof.
  intros. destruct (isExponential_uiso H H0). cat.
Qed.

Class HasExponentials (C : Cat) {hp : HasProducts C} : Type :=
{
  expOb : Ob C -> Ob C -> Ob C;
  eval : forall {X Y : Ob C}, Hom (prodOb (expOb X Y) X) Y;
  curry : forall {X Y Z : Ob C}, Hom (prodOb Z X) Y -> Hom Z (expOb X Y);
  Proper_curry :> forall X Y Z : Ob C, Proper (equiv ==> equiv) (@curry X Y Z);
  is_exponential : forall X Y : Ob C, isExponential X Y (expOb X Y) eval (@curry X Y)
}.

Arguments expOb {C hp HasExponentials} _ _.
Arguments eval  {C hp HasExponentials X Y}.
Arguments curry {C hp HasExponentials X Y Z} _.

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
  destruct he; unfold isExponential, setoid_unique in *; cbn in *.
  destruct (is_exponential0 X Y E f).
  split.
  - intros <-. apply H.
  - intros Heq. apply H0. assumption.
Qed.

Lemma computation_rule :
  forall {E : Ob C} (f : Hom (prodOb E X) Y),
    curry f ×' id X .> eval == f.
Proof.
  intros E f.
  rewrite <- universal_property.
  reflexivity.
Qed.

Lemma uniqueness_rule :
  forall {E : Ob C} (f : Hom (prodOb E X) Y) (g : Hom E (expOb X Y)),
    g ×' id X .> eval == f -> g == curry f.
Proof.
  intros.
  symmetry.
  rewrite universal_property.
  assumption.
Qed.

Definition uncurry (f : Hom X (expOb Y Z)) : Hom (prodOb X Y) Z := f ×' (id Y) .> eval.

#[export]
Instance Proper_uncurry : Proper (equiv ==> equiv) uncurry.
Proof.
  unfold Proper, respectful, uncurry. intros.
  cut (x ×' id Y == y ×' id Y).
    intro H'. rewrite H'. reflexivity.
    apply Proper_ProductFunctor_fmap; [assumption | reflexivity].
Qed.

Lemma curry_uncurry :
  forall f : Hom X (expOb Y Z),
    curry (uncurry f) == f.
Proof.
  unfold uncurry; destruct he; cbn; intros.
  do 2 red in is_exponential0.
  destruct (is_exponential0 Y Z X (f ×' id Y .> (eval0 _ _))) as [H1 H2].
  apply H2. reflexivity.
Qed.

End Exponential.

Lemma uncurry_curry :
  forall
    {C : Cat} {hp : HasProducts C} (he : HasExponentials C)
    (X Y Z : Ob C) (f : Hom (prodOb X Y) Z),
      uncurry (curry f) == f.
Proof.
  destruct he; cbn; intros. do 2 red in is_exponential0.
  unfold uncurry. destruct (is_exponential0 Y Z X f).
  exact H.
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
  destruct he; cbn; intros.
  do 2 red in is_exponential0.
  destruct (is_exponential0 _ _ _ (eval0 X Y)) as [H1 H2].
  apply (H2 (id _)). rewrite ProductFunctor_fmap_id.
  rewrite comp_id_l. reflexivity.
Qed.

Lemma curry_comp :
  forall (A : Ob C) (f : Hom Y Z) (g : Hom Z A),
    curry (X := X) (eval .> f .> g) == curry (eval .> f) .> curry (eval .> g).
Proof.
  intros. destruct he; cbn in *.
  destruct (is_exponential0 _ _ _ ((eval0 X Y .> f) .> g)).
  destruct (is_exponential0 _ _ _ (eval0 X Y .> f)).
  destruct (is_exponential0 _ _ _ (eval0 X Z .> g)).
  apply H0. rewrite <- (comp_id_l X).
  rewrite ProductFunctor_fmap_comp. rewrite comp_assoc.
  rewrite H3. rewrite <- comp_assoc. rewrite H1. reflexivity.
Qed.

Lemma uncurry_id :
  uncurry (id (expOb X Y)) == eval.
Proof.
  destruct he; cbn; intros.
  do 2 red in is_exponential0.
  destruct (is_exponential0 _ _ _ (eval0 X Y)) as [H1 H2].
  unfold uncurry. rewrite ProductFunctor_fmap_id. cat.
Qed.

End Exponential.

Ltac curry := intros; repeat
match goal with
| |- context [Proper] => proper; intros
| |- context [curry (eval .> (_ .> _))] =>
        rewrite <- (comp_assoc eval); rewrite curry_comp
| |- curry _ == id _ => rewrite <- curry_eval
| |- curry _ == curry _ => apply Proper_curry
| |- _ .> _ == _ .> _ => try (f_equiv; auto; fail)
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- ?x == ?x => reflexivity
end.

Lemma HasExponentials_unique :
  forall
    {C : Cat} {hp : HasProducts C}
    (he : HasExponentials C) (he' : HasExponentials C) (X Y : Ob C),
      @expOb C hp he X Y ~ @expOb C hp he' X Y.
Proof.
  intros. destruct he, he'. cbn in *.
  destruct (isExponential_uiso (is_exponential0 X Y) (is_exponential1 X Y)).
  cat.
Qed.

#[refine]
#[export]
Instance ExponentialFunctor
  {C : Cat} {hp : HasProducts C} {he : HasExponentials C} (X : Ob C) : Functor C C :=
{
  fob := fun Y : Ob C => expOb X Y;
  fmap := fun (A B : Ob C) (f : Hom A B) => curry (eval .> f)
}.
Proof. all: curry. Defined.

Module Universal.

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

Arguments expOb {C hp HasExponentials} _ _.
Arguments eval  {C hp HasExponentials X Y}.
Arguments curry {C hp HasExponentials X Y Z} _.

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
  forall {E : Ob C} (f : Hom (prodOb E X) Y),
    curry f ×' id X .> eval == f.
Proof.
  intros E f.
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

End Universal.

Module UniversalEquiv.

#[refine]
#[export]
Instance to (C : Cat) (hp : HasProducts C) (he : HasExponentials C)
  : Universal.HasExponentials C :=
{
  expOb := @expOb C hp he;
  eval := @eval C hp he;
  curry := @curry C hp he;
}.
Proof.
  split.
  - intros <-. apply computation_rule.
  - intros Heq. symmetry. apply uniqueness_rule. assumption.
Defined.

#[refine]
#[export]
Instance from (C : Cat) (hp : HasProducts C) (he : Universal.HasExponentials C)
  : HasExponentials C :=
{
  expOb := @Universal.expOb C hp he;
  eval := @Universal.eval C hp he;
  curry := @Universal.curry C hp he;
}.
Proof.
  unfold isExponential, setoid_unique.
  intros X Y E' eval'; split.
  - apply Universal.universal. reflexivity.
  - intros h <-. apply Universal.curry_uncurry.
Defined.

End UniversalEquiv.

Module Rules.

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

Arguments expOb {C hp HasExponentials} _ _.
Arguments eval  {C hp HasExponentials X Y}.
Arguments curry {C hp HasExponentials X Y Z} _.

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
  forall {E : Ob C} (f : Hom (prodOb E X) Y),
    curry f ×' id X .> eval == f.
Proof.
  intros E f.
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

End Rules.

Module RulesEquiv.

#[refine]
#[export]
Instance to (C : Cat) (hp : HasProducts C) (he : HasExponentials C)
  : Rules.HasExponentials C :=
{
  expOb := @expOb C hp he;
  eval := @eval C hp he;
  curry := @curry C hp he;
}.
Proof.
  - apply computation_rule.
  - apply uniqueness_rule.
Defined.

#[refine]
#[export]
Instance from (C : Cat) (hp : HasProducts C) (he : Rules.HasExponentials C)
  : HasExponentials C :=
{
  expOb := @Rules.expOb C hp he;
  eval := @Rules.eval C hp he;
  curry := @Rules.curry C hp he;
}.
Proof.
  unfold isExponential, setoid_unique.
  intros X Y E' eval'; split.
  - apply Rules.he_comp.
  - intros h <-. apply Rules.curry_uncurry.
Defined.

End RulesEquiv.