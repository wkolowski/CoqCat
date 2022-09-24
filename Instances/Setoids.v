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
Proof. now proper. Defined.

Arguments const _ [Y] _.

Lemma CoqSetoid_isMono :
  forall (X Y : Ob CoqSetoid) (f : Hom X Y),
    isMono f <-> injectiveS f.
Proof.
  unfold isMono, injectiveS; split; intros.
  - now specialize (H X (const X a) (const X a')); cbn in H; apply H.
  - now cbn; intros x; apply H, H0.
Defined.

Lemma CoqSetoid_isEpi :
  forall (X Y : Ob CoqSetoid) (f : Hom X Y),
    surjectiveS f -> isEpi f.
Proof.
  unfold isEpi, surjectiveS.
  cbn; intros X Y f Hsur Z g h Heq y.
  destruct (Hsur y) as [x <-].
  now apply Heq.
Defined.

Lemma CoqSetoid_isSec :
  forall (X Y : Ob CoqSetoid) (f : Hom X Y),
    isSec f -> injectiveS f.
Proof.
  intros.
  apply isMono_isSec in H.
  now apply CoqSetoid_isMono.
Defined.

Lemma CoqSetoid_isRet :
  forall (X Y : Ob CoqSetoid) (f : Hom X Y),
    isRet f <-> surjectiveS' f.
Proof.
  unfold isRet, surjectiveS.
  split; cbn.
  - intros [g H]. red.
    exists g.
    now setoid'.
  - intros (g & H1 & H2).
    now exists {| func := g; Proper_func := H1 |}.
Qed.

#[refine]
#[export]
Instance CoqSetoid_init : Setoid' :=
{
  carrier := Empty_set;
  setoid := {| equiv := fun (x y : Empty_set) => match x with end |}
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_create (X : Setoid') : SetoidHom CoqSetoid_init X :=
{
  func := fun e : Empty_set => match e with end
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance HasInit_CoqSetoid : HasInit CoqSetoid :=
{
  init := CoqSetoid_init;
  create := CoqSetoid_create;
}.
Proof. now setoid. Defined.

#[export]
Instance HasStrictInit_CoqSetoid : HasStrictInit CoqSetoid.
Proof.
  intros A f.
  exists (create A); split.
  - now intros x; destruct (f x).
  - now apply equiv_initial.
Defined.

#[refine]
#[export]
Instance CoqSetoid_term : Setoid' :=
{
  carrier := unit;
  setoid := {| equiv := fun _ _ => True |};
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_delete (X : Setoid') : SetoidHom X CoqSetoid_term :=
{
  func := fun _ => tt
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance HasTerm_CoqSetoid : HasTerm CoqSetoid :=
{
  term := CoqSetoid_term;
  delete := CoqSetoid_delete;
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_product (X Y : Setoid') : Setoid' :=
{
  carrier := X * Y;
  setoid := {| equiv := fun p1 p2 : X * Y =>
    @equiv _ (@setoid X) (fst p1) (fst p2) /\
    @equiv _ (@setoid Y) (snd p1) (snd p2) |}
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_outl (X Y : Setoid') : SetoidHom (CoqSetoid_product X Y) X :=
{
  func := fst
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_outr (X Y : Setoid') : SetoidHom (CoqSetoid_product X Y) Y :=
{
  func := snd
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_fpair
  (A B X : Setoid') (f : SetoidHom X A) (g : SetoidHom X B)
  : SetoidHom X (CoqSetoid_product A B) :=
{
  func := fun x : X => (f x, g x)
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance HasProducts_CoqSetoid : HasProducts CoqSetoid :=
{
  product := CoqSetoid_product;
  outl := CoqSetoid_outl;
  outr := CoqSetoid_outr;
  fpair := CoqSetoid_fpair
}.
Proof. all: now setoid'. Defined.

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
  split; red.
  - now intros [x | y].
  - now intros [x1 | y1] [x2 | y2].
  - now intros [x1 | y1] [x2 | y2] [x3 | y3]; setoid.
Defined.

#[refine]
#[export]
Instance CoqSetoid_finl (X Y : Setoid') : SetoidHom X (CoqSetoid_coproduct X Y) :=
{
  func := inl;
}.
Proof.
  now proper.
Defined.

#[refine]
#[export]
Instance CoqSetoid_finr (X Y : Setoid') : SetoidHom Y (CoqSetoid_coproduct X Y) :=
{
  func := inr;
}.
Proof.
  now proper.
Defined.

#[refine]
#[export]
Instance CoqSetoid_copair
  (A B X : Setoid') (f : SetoidHom A X) (g : SetoidHom B X)
  : SetoidHom (CoqSetoid_coproduct A B) X :=
{
  func := fun p : sum A B =>
    match p with
    | inl a => f a
    | inr b => g b
    end;
}.
Proof.
  now intros [a1 | b1] [a2 | b2]; cbn; setoid.
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
  split; cbn; [easy | easy |].
  intros P' h1 h2 HeqA HeqB [a | b].
  - now apply HeqA.
  - now apply HeqB.
Defined.

#[refine]
#[export]
Instance CoqSetoid_equalizer {X Y : Setoid'} (f g : SetoidHom X Y) : Setoid' :=
{
  carrier := {x : X | f x == g x};
  setoid := {| equiv := fun p1 p2 =>
    @equiv _ (@setoid X) (proj1_sig p1) (proj1_sig p2) |}
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance CoqSetoid_equalize
  {X Y : Setoid'} (f g : SetoidHom X Y)
  : SetoidHom (CoqSetoid_equalizer f g) X :=
{
  func := @proj1_sig _ _
}.
Proof. now setoid. Defined.

#[export]
Program Instance CoqSetoid_factorize
  {X Y : Setoid'} (f g : SetoidHom X Y)
  (E' : Setoid') (e' : SetoidHom E' X) (H : forall x : E', f (e' x) == g (e' x))
  : SetoidHom E' (CoqSetoid_equalizer f g) :=
{
  func := fun x => e' x
}.
Next Obligation. now proper. Defined.

#[refine]
#[export]
Instance HasEqualizers_CoqSetoid : HasEqualizers CoqSetoid :=
{
  equalizer := @CoqSetoid_equalizer;
  equalize := @CoqSetoid_equalize;
  factorize := @CoqSetoid_factorize;
}.
Proof.
  split; cbn.
  - now intros [x H]; cbn.
  - easy.
  - now intros E' e1 e2 Heq x; apply Heq.
Defined.

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
  split; red.
  - now constructor 1.
  - now constructor 3.
  - now econstructor 4; eauto.
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
Instance CoqSetoid_cofactorize
  (X Y : Setoid') (f g : SetoidHom X Y)
  (Q' : Setoid') (q' : SetoidHom Y Q') (H : forall x : X, q' (f x) == q' (g x))
  : SetoidHom (CoqSetoid_coequalizer f g) Q' :=
{
  func := q'
}.
Proof.
  intros x y Heq; cbn in *.
  induction Heq.
  - now rewrite H0.
  - easy.
  - easy.
  - now rewrite IHHeq1, IHHeq2.
Defined.

#[refine]
#[export]
Instance HasCoequalizers_CoqSetoid : HasCoequalizers CoqSetoid :=
{
  coequalizer := @CoqSetoid_coequalizer;
  coequalize := CoqSetoid_coequalize;
  cofactorize := CoqSetoid_cofactorize;
}.
Proof.
  split; cbn.
  - constructor 2.
  - easy.
  - easy.
Defined.

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
  exists (fun (f : forall j : J, A j) => f j).
  now proper.
Defined.

#[export]
Instance CoqSetoid_tuple
  {J : Set} {A : J -> Setoid'} {X : Setoid'}
  (f : forall j : J, SetoidHom X (A j))
  : SetoidHom X (CoqSetoid_indexedProduct A).
Proof.
  exists (fun x : X => (fun j : J => f j x)).
  now proper.
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
  split; red.
  - now intros [x x']; cbn.
  - intros [x x'] [y y']; cbn; intros [-> H]; split; [easy |].
    now eapply JMequiv_sym.
  - intros [x x'] [y y'] [z z']; cbn; intros [-> H1] [-> H2]; split; [easy |].
    now eapply (JMequiv_trans (eq_refl) (JMeq_refl) H1 H2).
Defined.

#[refine]
#[export]
Instance CoqSetoid_inj
  {J : Set} (A : J -> Setoid') (j : J) : SetoidHom (A j) (CoqSetoid_indexedCoproduct A) :=
{
  func := fun x : A j => existT _ j x
}.
Proof. now proper. Defined.

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
  intros [x x'] [y y']; cbn; intros [-> H].
  inversion H as [y'' Heq Hy'' H']; apply inj_pair2 in H'; subst.
  now rewrite Heq.
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
  now setoid.
Defined.

#[refine]
#[export]
Instance CoqSetoid_exponential_setoid (X Y : Setoid') : Setoid (SetoidHom X Y) :=
{
  equiv := fun f g : SetoidHom X Y => forall x : X, f x == g x
}.
Proof. now setoid. Defined.

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
  exists (fun fx : SetoidHom X Y * X => (fst fx) (snd fx)).
  intros [f1 x1] [f2 x2] [Heq1 Heq2]; cbn in *.
  transitivity (f2 x1).
  - now apply Heq1.
  - now rewrite Heq2.
Defined.

Definition CoqSetoid_curry_fun
  (X Y Z : Setoid') (f : SetoidHom (CoqSetoid_product Z X) Y)
  : Z -> (CoqSetoid_exponential X Y).
Proof.
  intros z.
  exists (fun x => f (z, x)).
  intros x1 x2 Heq.
  now apply Proper_func.
Defined.

#[export]
Instance CoqSetoid_curry
  (X Y Z : Setoid') (f : SetoidHom (CoqSetoid_product Z X) Y)
  : SetoidHom Z (CoqSetoid_exponential X Y).
Proof.
  exists (CoqSetoid_curry_fun f).
  intros z1 z2 Heq x; cbn.
  now apply Proper_func.
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