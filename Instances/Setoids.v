From Cat Require Export Cat.
From Cat Require Import Category.CartesianClosed.
From Cat.Universal Require Export
  Initial Terminal Product Coproduct Equalizer Coequalizer Exponential IndexedProduct IndexedCoproduct.

Set Implicit Arguments.

#[refine]
#[export]
Instance const (X Y : Setoid') (y : Y) : SetoidHom X Y :=
{
  func := fun _ => y
}.
Proof. setoid. Defined.

Arguments const _ [Y] _.

Lemma CoqSetoid_isMono :
  forall (X Y : Ob CoqSetoid) (f : Hom X Y),
    isMono f <-> injectiveS f.
Proof.
  unfold isMono, injectiveS; split; intros.
  - specialize (H X (const X a) (const X a')). now cbn in H; apply H.
  - cbn; intros x. apply H, H0.
Defined.

Lemma CoqSetoid_isEpi :
  forall (X Y : Ob CoqSetoid) (f : Hom X Y),
    surjectiveS f -> isEpi f.
Proof.
  unfold isEpi, surjectiveS; intros. cbn in *. intro.
  destruct (H x) as [a eq].
  rewrite (Proper_func g x), (Proper_func h x).
    apply H0.
    all: now rewrite eq.
Defined.

Lemma CoqSetoid_isSec :
  forall (X Y : Ob CoqSetoid) (f : Hom X Y),
    isSec f -> injectiveS f.
Proof.
  unfold isSec, injectiveS; intros.
  destruct H as [g H]. cbn in *.
  now rewrite <- (H a), <- (H a'), H0.
Defined.

Lemma CoqSetoid_isRet :
  forall (X Y : Ob CoqSetoid) (f : Hom X Y),
    isRet f <-> surjectiveS' f.
Proof.
  unfold isRet, surjectiveS; split; cbn; intros.
    destruct H as [g H]. red. exists g. setoid'.
    do 2 destruct H. exists {| func := x; Proper_func := H |}. cat.
Qed.

#[refine]
#[export]
Instance CoqSetoid_init : Setoid' :=
{
  carrier := Empty_set;
  setoid := {| equiv := fun (x y : Empty_set) => match x with end |}
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_create (X : Setoid') : SetoidHom CoqSetoid_init X :=
{
  func := fun e : Empty_set => match e with end
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance HasInit_CoqSetoid : HasInit CoqSetoid :=
{
  init := CoqSetoid_init;
  create := CoqSetoid_create;
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_term : Setoid' :=
{
  carrier := unit;
  setoid := {| equiv := fun _ _ => True |};
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_delete (X : Setoid') : SetoidHom X CoqSetoid_term :=
{
  func := fun _ => tt
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance HasTerm_CoqSetoid : HasTerm CoqSetoid :=
{
  term := CoqSetoid_term;
  delete := CoqSetoid_delete;
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_product (X Y : Setoid') : Setoid' :=
{
  carrier := X * Y;
  setoid := {| equiv := fun p1 p2 : X * Y =>
    @equiv _ (@setoid X) (fst p1) (fst p2) /\
    @equiv _ (@setoid Y) (snd p1) (snd p2) |}
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_outl (X Y : Setoid') : SetoidHom (CoqSetoid_product X Y) X :=
{
  func := fst
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_outr (X Y : Setoid') : SetoidHom (CoqSetoid_product X Y) Y :=
{
  func := snd
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_fpair
  (A B X : Setoid') (f : SetoidHom X A) (g : SetoidHom X B)
  : SetoidHom X (CoqSetoid_product A B) :=
{
  func := fun x : X => (f x, g x)
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance HasProducts_CoqSetoid : HasProducts CoqSetoid :=
{
  product := CoqSetoid_product;
  outl := CoqSetoid_outl;
  outr := CoqSetoid_outr;
  fpair := CoqSetoid_fpair
}.
Proof. all: setoid'. Defined.

#[refine]
#[export]
Instance CoqSetoid_coproduct (X Y : Setoid') : Setoid' :=
{
  carrier := sum X Y;
  setoid :=
  {|
    equiv := fun p1 p2 : sum X Y =>
      match p1, p2 with
      | inl x, inl x' => @equiv _ (@setoid X) x x'
      | inr y, inr y' => @equiv _ (@setoid Y) y y'
      | _, _ => False
      end
  |}
}.
Proof.
  setoid'; destruct x; try destruct y; try destruct z; setoid.
Defined.

#[export]
Instance CoqSetoid_finl (X Y : Setoid') : SetoidHom X (CoqSetoid_coproduct X Y).
Proof.
  split with inl. proper.
Defined.

#[export]
Instance CoqSetoid_finr (X Y : Setoid') : SetoidHom Y (CoqSetoid_coproduct X Y).
Proof.
  split with inr. proper.
Defined.

#[export]
Instance CoqSetoid_copair
  (A B X : Setoid') (f : SetoidHom A X) (g : SetoidHom B X)
  : SetoidHom (CoqSetoid_coproduct A B) X.
Proof.
  split with
  (
    fun p : sum A B =>
    match p with
    | inl a => f a
    | inr b => g b
    end
  ).
  proper. destruct x, y; setoid.
Defined.

#[refine]
#[export]
Instance HasCoproducts_CoqSetoid : HasCoproducts CoqSetoid :=
{
  coproduct := CoqSetoid_coproduct;
  finl := CoqSetoid_finl;
  finr := CoqSetoid_finr;
  copair := CoqSetoid_copair
}.
Proof.
  all: repeat
  match goal with
  | p : _ + _ |- _ => destruct p
  | _ => setoid'
  end.
Defined.

#[refine]
#[export]
Instance CoqSetoid_equalizer {X Y : Setoid'} (f g : SetoidHom X Y) : Setoid' :=
{
  carrier := {x : X | f x == g x};
  setoid := {| equiv := fun p1 p2 =>
    @equiv _ (@setoid X) (proj1_sig p1) (proj1_sig p2) |}
}.
Proof. setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_equalize
  {X Y : Setoid'} (f g : SetoidHom X Y)
  : SetoidHom (CoqSetoid_equalizer f g) X :=
{
  func := @proj1_sig _ _
}.
Proof. setoid. Defined.

#[export]
Program Instance factorize
  {X Y E' : Setoid'} (f g : SetoidHom X Y)
  (e' : SetoidHom E' X) (H : forall x : E', f (e' x) == g (e' x))
  : SetoidHom E' (CoqSetoid_equalizer f g) :=
{
  func := fun x => e' x
}.
Next Obligation. proper. Defined.

#[refine]
#[export]
Instance HasEqualizers_CoqSetoid : HasEqualizers CoqSetoid :=
{
  equalizer := @CoqSetoid_equalizer;
  equalize := @CoqSetoid_equalize;
}.
Proof.
Abort.

Inductive CoqSetoid_coeq_equiv {X Y : Setoid'} (f g : SetoidHom X Y) : Y -> Y -> Prop :=
| coeq_step :forall y y' : Y, y == y' -> CoqSetoid_coeq_equiv f g y y'
| coeq_quot : forall x : X, CoqSetoid_coeq_equiv f g (f x) (g x)
| coeq_sym :
  forall y y' : Y, CoqSetoid_coeq_equiv f g y y' -> CoqSetoid_coeq_equiv f g y' y
| coeq_trans :
  forall y1 y2 y3 : Y,
    CoqSetoid_coeq_equiv f g y1 y2 -> CoqSetoid_coeq_equiv f g y2 y3 ->
      CoqSetoid_coeq_equiv f g y1 y3.

#[refine]
#[export]
Instance CoqSetoid_coequalizer {X Y : Setoid'} (f g : SetoidHom X Y) : Setoid' :=
{
  carrier := Y;
  setoid := {| equiv := CoqSetoid_coeq_equiv f g |}
}.
Proof.
  solve_equiv.
    now apply coeq_step.
    now apply coeq_sym.
    eapply coeq_trans; eauto.
Defined.

#[refine]
#[export]
Instance CoqSetoid_coequalize
  (X Y : Setoid') (f g : SetoidHom X Y) : SetoidHom Y (CoqSetoid_coequalizer f g) :=
{
  func := fun y : Y => y
}.
Proof. now constructor. Defined.

#[refine]
#[export]
Instance cofactorize
  (X Y Q' : Setoid') (f g : SetoidHom X Y)
  (q' : SetoidHom Y Q') (H : forall x : X, q' (f x) == q' (g x))
  : SetoidHom (CoqSetoid_coequalizer f g) Q' :=
{
  func := q'
}.
Proof. proper. induction H0; subst; setoid'. Defined.

#[refine]
#[export]
Instance HasCoequalizers_CoqSetoid : HasCoequalizers CoqSetoid :=
{
  coequalizer := @CoqSetoid_coequalizer;
  coequalize := CoqSetoid_coequalize
}.
Proof.
Abort.

#[refine]
#[export]
Instance CoqSetoid_indexedProduct {J : Set} (A : J -> Setoid') : Setoid' :=
{
  carrier := forall j : J, A j;
  setoid :=
  {|
    equiv := fun f g : forall j : J, A j => forall j : J, @equiv _ (A j) (f j) (g j)
  |}
}.
Proof.
  now split; red; intros; rewrite ?H, ?H0.
Defined.

#[export]
Instance CoqSetoid_out
  {J : Set} (A : J -> Setoid') (j : J) : SetoidHom (CoqSetoid_indexedProduct A) (A j).
Proof.
  split with (fun (f : forall j : J, A j) => f j). proper.
Defined.

#[export]
Instance CoqSetoid_tuple
  {J : Set} {A : J -> Setoid'} {X : Setoid'}
  (f : forall j : J, SetoidHom X (A j))
  : SetoidHom X (CoqSetoid_indexedProduct A).
Proof.
  split with (fun x : X => (fun j : J => f j x)). proper.
Defined.

#[refine]
#[export]
Instance HasIndexedProducts_CoqSetoid : HasIndexedProducts CoqSetoid :=
{
  indexedProduct := @CoqSetoid_indexedProduct;
  out := @CoqSetoid_out;
  tuple := @CoqSetoid_tuple
}.
Proof.
  now split; cbn.
Defined.

#[refine]
#[export]
Instance CoqSetoid_indexedCoproduct {J : Set} (A : J -> Setoid') : Setoid' :=
{
  carrier := {j : J & A j};
  setoid :=
  {|
    equiv := fun x y : {j : J & A j} =>
      projT1 x = projT1 y /\ @JMequiv _ (A (projT1 x)) (projT2 x) (A (projT1 y)) (projT2 y)
  |}
}.
Proof.
  split; red; destruct x; try destruct y; try destruct z;
  cbn; intros.
    easy.
    destruct H; subst. split; auto. inversion H0; subst.
      constructor. apply inj_pair2 in H.
      now rewrite H1, <- H.
    destruct H, H0; split.
      now rewrite H, H0.
      subst. eapply (JMequiv_trans (eq_refl) (JMeq_refl) H1 H2).
Defined.

#[refine]
#[export]
Instance CoqSetoid_inj
  {J : Set} (A : J -> Setoid') (j : J) : SetoidHom (A j) (CoqSetoid_indexedCoproduct A) :=
{
  func := fun x : A j => existT _ j x
}.
Proof. proper. Defined.

#[refine]
#[export]
Instance CoqSetoid_cotuple
  {J : Set} {A : J -> Setoid'} {X : Setoid'}
  (f : forall j : J, SetoidHom (A j) X)
  : SetoidHom (CoqSetoid_indexedCoproduct A) X :=
{
  func := fun x => f (projT1 x) (projT2 x)
}.
Proof.
  proper.
  destruct x, y. cbn in *. destruct H; subst. inversion H0.
  apply inj_pair2 in H. subst. now rewrite H1.
Defined.

#[refine]
#[export]
Instance HasIndexedCoproducts_CoqSetoid : HasIndexedCoproducts CoqSetoid :=
{
  indexedCoproduct := @CoqSetoid_indexedCoproduct;
  inj := @CoqSetoid_inj;
  cotuple := @CoqSetoid_cotuple
}.
Proof.
  setoid.
Defined.

#[refine]
#[export]
Instance CoqSetoid_exponential_setoid (X Y : Setoid') : Setoid (SetoidHom X Y) :=
{
  equiv := fun f g : SetoidHom X Y => forall x : X, f x == g x
}.
Proof. setoid. Defined.

#[export]
Instance CoqSetoid_exponential (X Y : Setoid') : Setoid' :=
{
  carrier := SetoidHom X Y;
  setoid := CoqSetoid_exponential_setoid X Y
}.

#[export]
Instance CoqSetoid_eval
  (X Y : Setoid') : SetoidHom (product (CoqSetoid_exponential X Y) X) Y.
Proof.
  split with (fun fx : SetoidHom X Y * X => (fst fx) (snd fx)).
  proper. destruct x, y, H; cbn in *. setoid.
Defined.

Definition CoqSetoid_curry_fun
  (X Y Z : Setoid') (f : SetoidHom (CoqSetoid_product Z X) Y)
  : Z -> (CoqSetoid_exponential X Y).
Proof.
  intro z. destruct f as [f Hf]; do 2 red in Hf; cbn in *.
  split with (fun x : X => f (z, x)). do 2 red. intros.
  now apply Hf.
Defined.

#[export]
Instance CoqSetoid_curry
  (X Y Z : Setoid') (f : SetoidHom (CoqSetoid_product Z X) Y)
  : SetoidHom Z (CoqSetoid_exponential X Y).
Proof.
  split with (CoqSetoid_curry_fun f). do 2 red. intros.
  setoidhom f; unfold CoqSetoid_curry_fun; cbn in *. intro x'.
  now apply f_pres_equiv.
Defined.

#[refine]
#[export]
Instance HasExponentials_CoqSetoid : HasExponentials CoqSetoid :=
{
  exponential := CoqSetoid_exponential;
  eval := CoqSetoid_eval;
  curry := CoqSetoid_curry
}.
Proof.
  split; cbn.
  - now intros E' [f Hf] [e' a]; cbn.
  - now intros E' f g H e' a; apply (H (e', a)).
Defined.

#[export]
Instance CoqSetoid_CartesianClosed : CartesianClosed CoqSetoid :=
{
  HasTerm_CartesianClosed := HasTerm_CoqSetoid;
  HasProducts_CartesianClosed := HasProducts_CoqSetoid;
  HasExponentials_CartesianClosed := HasExponentials_CoqSetoid;
}.

#[export]
Instance HomFunctor_fob (C : Cat) (X : Ob C) : Ob C -> Setoid' := fun Y : Ob C =>
{|
  carrier := Hom X Y;
  setoid := HomSetoid X Y
|}.

#[export]
Instance HomFunctor_fmap
  (C : Cat) (X : Ob C)
  : forall Y Z : Ob C, Hom Y Z -> SetoidHom (HomFunctor_fob C X Y) (HomFunctor_fob C X Z).
Proof.
  intros Y Z g. split with (fun f : Hom X Y => f .> g).
  proper.
Defined.

#[refine]
#[export]
Instance HomFunctor (C : Cat) (X : Ob C) : Functor C CoqSetoid :=
{
  fob := HomFunctor_fob C X;
  fmap := HomFunctor_fmap C X;
}.
Proof. proper. all: cat. Defined.