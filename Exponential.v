Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Definition exponential_skolem {C : Cat} {hp : has_products C}
  (X Y E : Ob C) (eval : Hom (prodOb E X) Y)
  (curry : forall E' : Ob C, Hom (prodOb E' X) Y -> Hom E' E) : Prop :=
    forall (E' : Ob C) (eval' : Hom (prodOb E' X) Y),
      setoid_unique (fun u : Hom E' E =>
        ProductFunctor_fmap u (id X) .> eval == eval') (curry E' eval').

Class has_exponentials (C : Cat) {hp : has_products C} : Type :=
{
    expOb : Ob C -> Ob C -> Ob C;
    eval : forall X Y : Ob C,
      Hom (prodOb (expOb X Y) X) Y;
    curry : forall {X Y Z : Ob C},
      Hom (prodOb Z X) Y -> Hom Z (expOb X Y);
    curry_Proper :> forall X Y Z : Ob C,
      Proper (equiv ==> equiv) (@curry X Y Z);
    is_exponential : forall (X Y : Ob C),
      exponential_skolem X Y (expOb X Y) (eval X Y) (@curry X Y)
}.

Arguments expOb {C hp has_exponentials} _ _.
Arguments eval  {C hp has_exponentials X Y}.
Arguments curry {C hp has_exponentials X Y Z} _.

Definition uncurry
    {C : Cat} {hp : has_products C} {he : has_exponentials C}
    {X Y Z : Ob C} (f : Hom Z (expOb X Y)) : Hom (prodOb Z X) Y
    := f ×' (id X) .> eval.

Instance uncurry_Proper :
  forall (C : Cat) (hp : has_products C) (he : has_exponentials C)
    (X Y Z : Ob C), Proper (equiv ==> equiv) (@uncurry C hp he X Y Z).
Proof.
  unfold Proper, respectful, uncurry. intros.
  cut (x ×' id X == y ×' id X).
    intro H'. rewrite H'. reflexivity.
    apply ProductFunctor_fmap_Proper; [assumption | reflexivity].
Qed.

Theorem curry_uncurry :
  forall (C : Cat) (hp : has_products C) (he : has_exponentials C)
    (X Y Z : Ob C) (f : Hom X (expOb Y Z)),
      curry (uncurry f) == f.
Proof.
  unfold uncurry; destruct he; simpl; intros.
  do 2 red in is_exponential0.
  destruct (is_exponential0 Y Z X (f ×' id Y .> (eval0 _ _))) as [H1 H2].
  apply H2. reflexivity.
Qed.

Theorem uncurry_curry :
  forall (C : Cat) (hp : has_products C) (he : has_exponentials C)
    (X Y Z : Ob C) (f : Hom (prodOb X Y) Z),
      uncurry (curry f) == f.
Proof.
  destruct he; simpl; intros. do 2 red in is_exponential0.
  unfold uncurry. destruct (is_exponential0 Y Z X f).
  exact H.
Qed.

Theorem curry_eval :
  forall (C : Cat) (hp : has_products C) (he : has_exponentials C)
    (X Y : Ob C), curry eval == id (expOb X Y).
Proof.
  destruct he; simpl; intros.
  do 2 red in is_exponential0.
  destruct (is_exponential0 _ _ _ (eval0 X Y)) as [H1 H2].
  apply (H2 (id _)). rewrite ProductFunctor_fmap_pres_id.
  rewrite id_left. reflexivity.
Qed.

Theorem curry_comp :
  forall (C : Cat) (hp : has_products C) (he : has_exponentials C)
    (X Y Z A : Ob C) (f : Hom Y Z) (g : Hom Z A),
      @curry C hp he X A _ (eval .> f .> g) == curry (eval .> f) .> curry (eval .> g).
Proof.
  intros. destruct he; simpl in *.
  destruct (is_exponential0 _ _ _ ((eval0 X Y .> f) .> g)).
  destruct (is_exponential0 _ _ _ (eval0 X Y .> f)).
  destruct (is_exponential0 _ _ _ (eval0 X Z .> g)).
  apply H0. rewrite <- (id_left X).
  rewrite ProductFunctor_fmap_pres_comp. rewrite comp_assoc.
  rewrite H3. rewrite <- comp_assoc. rewrite H1. reflexivity.
Qed.

Theorem uncurry_id :
  forall (C : Cat) (hp : has_products C) (he : has_exponentials C)
    (X Y : Ob C), uncurry (id (expOb X Y)) == eval.
Proof.
  destruct he; simpl; intros.
  do 2 red in is_exponential0.
  destruct (is_exponential0 _ _ _ (eval0 X Y)) as [H1 H2].
  unfold uncurry. rewrite ProductFunctor_fmap_pres_id. cat.
Qed.

Ltac curry := intros; repeat
match goal with
    | |- context [Proper] => proper; intros
    | |- context [curry (eval .> (_ .> _))] =>
        rewrite <- (comp_assoc eval); rewrite curry_comp
    | |- curry _ == id _ => rewrite <- curry_eval
    | |- curry _ == curry _ => apply curry_Proper
    | |- _ .> _ == _ .> _ => try (f_equiv; auto; fail)
    | |- context [id _ .> _] => rewrite id_left
    | |- context [_ .> id _] => rewrite id_right
    | |- ?x == ?x => reflexivity
end.

Theorem exponential_skolem_uiso :
  forall (C : Cat) (hp : has_products C) (X Y : Ob C)
  (E : Ob C) (eval : Hom (prodOb E X) Y)
  (curry : forall Z : Ob C, Hom (prodOb Z X) Y -> Hom Z E)
  (E' : Ob C) (eval' : Hom (prodOb E' X) Y)
  (curry' : forall Z : Ob C, Hom (prodOb Z X) Y -> Hom Z E'),
    exponential_skolem X Y E eval curry ->
    exponential_skolem X Y E' eval' curry' ->
      exists !! f : Hom E E', Iso f /\
        f ×' id X .> eval' == eval.
Proof.
  intros. do 2 red in H. do 2 red in H0.
  exists (curry' E eval0). repeat split.
    red. exists (curry0 E' eval').
    split.
      destruct (H E eval0) as [H1 H2].
        rewrite <- (H2 (curry' E eval0 .> curry0 E' eval')).
          rewrite (H2 (id E)).
            reflexivity.
            rewrite ProductFunctor_fmap_pres_id, id_left. reflexivity.
          rewrite ProductFunctor_fmap_pres_comp_l.
            destruct (H E' eval'), (H0 E eval0).
              rewrite comp_assoc. rewrite H3. rewrite H5. reflexivity.
      destruct (H0 E' eval') as [H1 H2].
        rewrite <- (H2 (curry0 E' eval' .> curry' E eval0)).
          rewrite (H2 (id E')).
            reflexivity.
            rewrite ProductFunctor_fmap_pres_id, id_left. reflexivity.
          rewrite ProductFunctor_fmap_pres_comp_l.
            destruct (H E' eval'), (H0 E eval0).
              rewrite comp_assoc. rewrite H5. rewrite H3. reflexivity.
    intros. edestruct H0. apply H1.
    intros. edestruct H0. apply H3. rewrite <- H2. apply comp_Proper; cat.
      apply ProductFunctor_fmap_Proper; cat. rewrite H3; cat.
Qed.

Arguments exponential_skolem_uiso {C hp X Y E eval curry E' eval' curry'} _ _.

Theorem exponential_skolem_iso :
  forall (C : Cat) (hp : has_products C) (X Y : Ob C)
  (E : Ob C) (eval : Hom (prodOb E X) Y)
  (curry : forall Z : Ob C, Hom (prodOb Z X) Y -> Hom Z E)
  (E' : Ob C) (eval' : Hom (prodOb E' X) Y)
  (curry' : forall Z : Ob C, Hom (prodOb Z X) Y -> Hom Z E'),
    exponential_skolem X Y E eval curry ->
    exponential_skolem X Y E' eval' curry' ->
      E ~ E'.
Proof.
  intros. destruct (exponential_skolem_uiso H H0). cat.
Qed.

Theorem has_exponentials_unique :
  forall (C : Cat) (hp : has_products C)
  (he : has_exponentials C) (he' : has_exponentials C) (X Y : Ob C),
      @expOb C hp he X Y ~ @expOb C hp he' X Y.
Proof.
  intros. destruct he, he'. simpl in *.
  destruct (exponential_skolem_uiso
    (is_exponential0 X Y) (is_exponential1 X Y)).
  cat.
Qed.

#[refine]
Instance ExponentialFunctor
  (C : Cat) (hp : has_products C) (he : has_exponentials C)
  (X : Ob C) : Functor C C :=
{
    fob := fun Y : Ob C => expOb X Y;
    fmap := fun (A B : Ob C) (f : Hom A B) => curry (eval .> f)
}.
Proof. all: curry. Defined.