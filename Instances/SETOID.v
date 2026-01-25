From Cat Require Export Cat.
From Cat Require Import Category.CartesianClosed.
From Cat.Universal Require Export
  Initial Terminal Product Coproduct Equalizer Coequalizer Pullback Pushout Exponential
  IndexedProduct IndexedCoproduct.

Set Implicit Arguments.

#[export]
Instance SETOID_sumprod (A B : Setoid') : Setoid' :=
{
  carrier := sumprod A B;
  setoid := Setoid_sumprod A B;
}.

#[refine]
#[export]
Instance SETOID_inl' (A B : Setoid') : SetoidHom A (SETOID_sumprod A B) :=
{
  func := @inl' A B;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance SETOID_inr' (A B : Setoid') : SetoidHom B (SETOID_sumprod A B) :=
{
  func := @inr' A B;
}.
Proof. easy. Defined.

#[export]
Instance PROP : Setoid' :=
{
  carrier := Prop;
  setoid := Setoid_Prop;
}.

#[refine]
#[export]
Instance const (X Y : Setoid') (y : Y) : SetoidHom X Y :=
{
  func := fun _ => y
}.
Proof. now proper. Defined.

Arguments const _ [Y] _.

Lemma SETOID_isMono :
  forall (X Y : Ob SETOID) (f : Hom X Y),
    isMono f <-> injectiveS f.
Proof.
  unfold isMono, injectiveS; split; intros.
  - now specialize (H X (const X a) (const X a')); cbn in H; apply H.
  - now cbn; intros x; apply H, H0.
Defined.

Lemma SETOID_isEpi_surjectiveS :
  forall (X Y : Ob SETOID) (f : Hom X Y),
    surjectiveS f -> isEpi f.
Proof.
  unfold isEpi, surjectiveS.
  cbn; intros X Y f Hsur Z g h Heq y.
  destruct (Hsur y) as [x <-].
  now apply Heq.
Defined.

Lemma SETOID_surjectiveS_isEpi :
  forall (X Y : Ob SETOID) (f : Hom X Y),
    isEpi f -> surjectiveS f.
Proof.
  unfold isEpi, surjectiveS.
  cbn; intros X Y f HEpi y.
  pose (g := (fun y => exists a : X, f a == y) : Y -> PROP).
  assert (Proper_g : Proper (equiv ==> equiv) g)
    by now intros y1 y2 Heq; unfold g; cbn; setoid_rewrite Heq.
  pose (h := (fun _ : Y => True) : Y -> PROP).
  assert (Proper_h : Proper (equiv ==> equiv) h)
    by (cbn; firstorder).
  pose (g' := {| func := g; Proper_func := Proper_g; |}).
  pose (h' := {| func := h; Proper_func := Proper_h; |}).
  specialize (HEpi PROP g' h').
  unfold g', g, h', h in HEpi; cbn in HEpi.
  rewrite HEpi; [easy |].
  now intuition eexists.
Defined.

Lemma SETOID_isEpi :
  forall (X Y : Ob SETOID) (f : Hom X Y),
    isEpi f <-> surjectiveS f.
Proof.
  split.
  - now apply SETOID_surjectiveS_isEpi.
  - now apply SETOID_isEpi_surjectiveS.
Qed.

#[export]
Instance SETOID_init : Setoid' :=
{
  carrier := Empty_set;
  setoid := Setoid_Empty;
}.

#[refine]
#[export]
Instance SETOID_create (X : Setoid') : SetoidHom SETOID_init X :=
{
  func := fun e : Empty_set => match e with end
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance HasInit_SETOID : HasInit SETOID :=
{
  init := SETOID_init;
  create := SETOID_create;
}.
Proof. now setoid. Defined.

#[export]
Instance HasStrictInit_SETOID : HasStrictInit SETOID.
Proof.
  intros A f.
  exists (create A); split.
  - now intros x; destruct (f x).
  - now apply equiv_initial.
Defined.

#[export]
Instance SETOID_term : Setoid' :=
{
  carrier := unit;
  setoid := Setoid_unit;
}.

#[refine]
#[export]
Instance SETOID_delete (X : Setoid') : SetoidHom X SETOID_term :=
{
  func := fun _ => tt
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance HasTerm_SETOID : HasTerm SETOID :=
{
  term := SETOID_term;
  delete := SETOID_delete;
}.
Proof. now setoid. Defined.

#[export]
Instance SETOID_product (X Y : Setoid') : Setoid' :=
{
  carrier := X * Y;
  setoid := Setoid_prod X Y;
}.

#[refine]
#[export]
Instance SETOID_outl (X Y : Setoid') : SetoidHom (SETOID_product X Y) X :=
{
  func := fst
}.
Proof. now intros [] []; cbn. Defined.

#[refine]
#[export]
Instance SETOID_outr (X Y : Setoid') : SetoidHom (SETOID_product X Y) Y :=
{
  func := snd
}.
Proof. now intros [] []; cbn. Defined.

#[refine]
#[export]
Instance SETOID_fpair
  (A B X : Setoid') (f : SetoidHom X A) (g : SetoidHom X B)
  : SetoidHom X (SETOID_product A B) :=
{
  func := fun x : X => (f x, g x)
}.
Proof. now setoid. Defined.

#[refine]
#[export]
Instance HasProducts_SETOID : HasProducts SETOID :=
{
  product := SETOID_product;
  outl := SETOID_outl;
  outr := SETOID_outr;
  fpair := SETOID_fpair
}.
Proof.
  now split; cbn.
Defined.

#[export]
Instance SETOID_coproduct (X Y : Setoid') : Setoid' :=
{
  carrier := sum X Y;
  setoid := Setoid_sum X Y;
}.

#[refine]
#[export]
Instance SETOID_finl (X Y : Setoid') : SetoidHom X (SETOID_coproduct X Y) :=
{
  func := inl;
}.
Proof.
  now proper.
Defined.

#[refine]
#[export]
Instance SETOID_finr (X Y : Setoid') : SetoidHom Y (SETOID_coproduct X Y) :=
{
  func := inr;
}.
Proof.
  now proper.
Defined.

#[refine]
#[export]
Instance SETOID_copair
  (A B X : Setoid') (f : SetoidHom A X) (g : SetoidHom B X)
  : SetoidHom (SETOID_coproduct A B) X :=
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
Instance HasCoproducts_SETOID : HasCoproducts SETOID :=
{
  coproduct := SETOID_coproduct;
  finl := SETOID_finl;
  finr := SETOID_finr;
  copair := SETOID_copair
}.
Proof.
  split; cbn; [easy | easy |].
  intros P' h1 h2 HeqA HeqB [a | b].
  - now apply HeqA.
  - now apply HeqB.
Defined.

#[export]
Instance SETOID_equalizer {X Y : Setoid'} (f g : SetoidHom X Y) : Setoid' :=
{
  carrier := {x : X | f x == g x};
  setoid := Setoid_sig X;
}.

#[refine]
#[export]
Instance SETOID_equalize
  {X Y : Setoid'} (f g : SetoidHom X Y)
  : SetoidHom (SETOID_equalizer f g) X :=
{
  func := @proj1_sig _ _
}.
Proof. now setoid. Defined.

#[export]
Program Instance SETOID_factorize
  {X Y : Setoid'} {f g : SetoidHom X Y}
  {E' : Setoid'} (e' : SetoidHom E' X) (Heq : forall x : E', f (e' x) == g (e' x))
  : SetoidHom E' (SETOID_equalizer f g) :=
{
  func := fun x => e' x
}.
Next Obligation. now proper. Defined.

#[refine]
#[export]
Instance HasEqualizers_SETOID : HasEqualizers SETOID :=
{
  equalizer := @SETOID_equalizer;
  equalize := @SETOID_equalize;
  factorize := @SETOID_factorize;
}.
Proof.
  split; cbn.
  - now intros [x H]; cbn.
  - easy.
  - now intros E' e1 e2 Heq x; apply Heq.
Defined.

Inductive SETOID_coeq_equiv {X Y : Setoid'} (f g : SetoidHom X Y) : Y -> Y -> Prop :=
| coeq_step : forall y y' : Y, y == y' -> SETOID_coeq_equiv f g y y'
| coeq_quot : forall x : X, SETOID_coeq_equiv f g (f x) (g x)
| coeq_sym  :
  forall y y' : Y, SETOID_coeq_equiv f g y y' -> SETOID_coeq_equiv f g y' y
| coeq_trans :
  forall y1 y2 y3 : Y,
    SETOID_coeq_equiv f g y1 y2 -> SETOID_coeq_equiv f g y2 y3 ->
      SETOID_coeq_equiv f g y1 y3.

#[refine]
#[export]
Instance SETOID_coequalizer {X Y : Setoid'} (f g : SetoidHom X Y) : Setoid' :=
{
  carrier := Y;
  setoid := {| equiv := SETOID_coeq_equiv f g |}
}.
Proof.
  split; red.
  - now constructor 1.
  - now constructor 3.
  - now econstructor 4; eauto.
Defined.

#[refine]
#[export]
Instance SETOID_coequalize
  (X Y : Setoid') (f g : SetoidHom X Y) : SetoidHom Y (SETOID_coequalizer f g) :=
{
  func := fun y : Y => y
}.
Proof. now constructor. Defined.

#[refine]
#[export]
Instance SETOID_cofactorize
  (X Y : Setoid') (f g : SetoidHom X Y)
  (Q' : Setoid') (q' : SetoidHom Y Q') (H : forall x : X, q' (f x) == q' (g x))
  : SetoidHom (SETOID_coequalizer f g) Q' :=
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
Instance HasCoequalizers_SETOID : HasCoequalizers SETOID :=
{
  coequalizer := @SETOID_coequalizer;
  coequalize := SETOID_coequalize;
  cofactorize := SETOID_cofactorize;
}.
Proof.
  split; cbn.
  - constructor 2.
  - easy.
  - easy.
Defined.

#[export]
Instance SETOID_indexedProduct {J : Type} (A : J -> Setoid') : Setoid' :=
{
  carrier := forall j : J, A j;
  setoid := Setoid_forall A;
}.

#[export]
Instance SETOID_out
  {J : Type} (A : J -> Setoid') (j : J) : SetoidHom (SETOID_indexedProduct A) (A j).
Proof.
  exists (fun (f : forall j : J, A j) => f j).
  now proper.
Defined.

#[export]
Instance SETOID_tuple
  {J : Type} {A : J -> Setoid'} {X : Setoid'}
  (f : forall j : J, SetoidHom X (A j))
  : SetoidHom X (SETOID_indexedProduct A).
Proof.
  exists (fun x : X => (fun j : J => f j x)).
  now proper.
Defined.

#[refine]
#[export]
Instance HasIndexedProducts_SETOID : HasIndexedProducts SETOID :=
{
  indexedProduct := @SETOID_indexedProduct;
  out := @SETOID_out;
  tuple := @SETOID_tuple
}.
Proof.
  now split; cbn.
Defined.

#[export]
Instance SETOID_indexedCoproduct {J : Type} (A : J -> Setoid') : Setoid' :=
{
  carrier := {j : J & A j};
  setoid := Setoid_sigT A;
}.

#[refine]
#[export]
Instance SETOID_inj
  {J : Type} (A : J -> Setoid') (j : J) : SetoidHom (A j) (SETOID_indexedCoproduct A) :=
{
  func := fun x : A j => existT _ j x
}.
Proof.
  now intros a1 a2 Heq; cbn; exists eq_refl.
Defined.

#[refine]
#[export]
Instance SETOID_cotuple
  {J : Type} {A : J -> Setoid'} {X : Setoid'}
  (f : forall j : J, SetoidHom (A j) X)
  : SetoidHom (SETOID_indexedCoproduct A) X :=
{
  func := fun x => f (projT1 x) (projT2 x)
}.
Proof.
  now intros [x x'] [y y']; cbn; intros [-> ->].
Defined.

#[refine]
#[export]
Instance HasIndexedCoproducts_SETOID : HasIndexedCoproducts SETOID :=
{
  indexedCoproduct := @SETOID_indexedCoproduct;
  inj := @SETOID_inj;
  cotuple := @SETOID_cotuple
}.
Proof.
  split; cbn.
  - easy.
  - now intros X h1 h2 Heq [x x'].
Defined.

#[export]
Instance SETOID_exponential (X Y : Setoid') : Setoid' :=
{
  carrier := SetoidHom X Y;
  setoid := Setoid_SetoidHom X Y;
}.

#[export]
Instance SETOID_eval
  (X Y : Setoid') : SetoidHom (product (SETOID_exponential X Y) X) Y.
Proof.
  exists (fun fx : SetoidHom X Y * X => (fst fx) (snd fx)).
  intros [f1 x1] [f2 x2] [Heq1 Heq2]; cbn in *.
  transitivity (f2 x1).
  - now apply Heq1.
  - now rewrite Heq2.
Defined.

Definition SETOID_curry_fun
  (X Y Z : Setoid') (f : SetoidHom (SETOID_product Z X) Y)
  : Z -> (SETOID_exponential X Y).
Proof.
  intros z.
  exists (fun x => f (z, x)).
  intros x1 x2 Heq.
  now apply Proper_func.
Defined.

#[export]
Instance SETOID_curry
  (X Y Z : Setoid') (f : SetoidHom (SETOID_product Z X) Y)
  : SetoidHom Z (SETOID_exponential X Y).
Proof.
  exists (SETOID_curry_fun f).
  intros z1 z2 Heq x; cbn.
  now apply Proper_func.
Defined.

#[refine]
#[export]
Instance HasExponentials_SETOID : HasExponentials SETOID :=
{
  exponential := SETOID_exponential;
  eval := SETOID_eval;
  curry := SETOID_curry
}.
Proof.
  split; cbn.
  - now intros E' [f Hf] [e' a]; cbn.
  - now intros E' f g H e' a; apply (H (e', a)).
Defined.

#[export]
Instance SETOID_CartesianClosed : CartesianClosed SETOID :=
{
  HasTerm_CartesianClosed := HasTerm_SETOID;
  HasProducts_CartesianClosed := HasProducts_SETOID;
  HasExponentials_CartesianClosed := HasExponentials_SETOID;
}.

Record SETOID_pullback'
  {A B X : Setoid'} (f : SetoidHom A X) (g : SetoidHom B X) : Type := triple
{
  pullL : A;
  pullR : B;
  ok : f pullL == g pullR;
}.

Arguments triple {A B X f g} _ _ _.
Arguments pullL  {A B X f g} _.
Arguments pullR  {A B X f g} _.
Arguments ok     {A B X f g} _.

#[refine]
#[export]
Instance SETOID_pullback
  {A B X : Setoid'} (f : SetoidHom A X) (g : SetoidHom B X) : Setoid' :=
{
  carrier := SETOID_pullback' f g;
}.
Proof.
  unshelve esplit.
  - refine (fun x y => pullL x == pullL y /\ pullR x == pullR y).
  - split; red.
    + easy.
    + easy.
    + now intros x y z [-> ->] [-> ->].
Defined.

#[refine]
#[export]
Instance SETOID_pullL
  {A B X : Setoid'} {f : SetoidHom A X} {g : SetoidHom B X}
  : SetoidHom (SETOID_pullback f g) A :=
{
  func := pullL
}.
Proof.
  now intros x y [H _]; cbn.
Defined.

#[refine]
#[export]
Instance SETOID_pullR
  {A B X : Setoid'} {f : SetoidHom A X} {g : SetoidHom B X}
  : SetoidHom (SETOID_pullback f g) B :=
{
  func := pullR;
}.
Proof.
  now intros x y [_ H]; cbn.
Defined.

#[refine]
#[export]
Instance SETOID_triple
  {A B X : Setoid'} {f : SetoidHom A X} {g : SetoidHom B X}
  {Γ : Setoid'} (a : SetoidHom Γ A) (b : SetoidHom Γ B) (Heq : forall x : Γ, f (a x) == g (b x))
  : SetoidHom Γ (SETOID_pullback f g) :=
{
   func := fun x => triple (a x) (b x) (Heq x);
}.
Proof.
  intros x y H; cbn.
  now rewrite H.
Defined.

#[refine]
#[export]
Instance HasPullbacks_SETOID : HasPullbacks SETOID :=
{
  pullback := @SETOID_pullback;
  pullL := @SETOID_pullL;
  pullR := @SETOID_pullR;
  triple := @SETOID_triple;
}.
Proof.
  split; cbn.
  - now apply ok.
  - easy.
  - easy.
  - easy.
Defined.

Section Pushout.

Context
  {A B Γ : Setoid'} {f : SetoidHom Γ A} {g : SetoidHom Γ B}.

Inductive SETOID_pushout_equiv : A + B -> A + B -> Prop :=
| CSpe_glue  : forall x : Γ, SETOID_pushout_equiv (inl (f x)) (inr (g x))
| CSpe_refl  : forall x y : A + B, x == y -> SETOID_pushout_equiv x y
| CSpe_sym   : forall x y : A + B, SETOID_pushout_equiv y x -> SETOID_pushout_equiv x y
| CSpe_trans :
  forall x y z : A + B,
    SETOID_pushout_equiv x y ->
    SETOID_pushout_equiv y z ->
      SETOID_pushout_equiv x z.

#[refine]
#[export]
Instance SETOID_pushout : Setoid' :=
{
  carrier := SETOID_coproduct A B;
  setoid :=
  {|
    equiv := SETOID_pushout_equiv;
  |};
}.
Proof.
  split; red.
  - now intros; apply CSpe_refl.
  - now intros; apply CSpe_sym.
  - now intros; apply CSpe_trans with  y.
Defined.

#[refine]
#[export]
Instance SETOID_pushl : SetoidHom A SETOID_pushout :=
{
  func := inl;
}.
Proof.
  intros a1 a2 Heq; cbn.
  now constructor.
Defined.

#[refine]
#[export]
Instance SETOID_pushr : SetoidHom B SETOID_pushout :=
{
  func := inr;
}.
Proof.
  intros b1 b2 Heq; cbn.
  now constructor.
Defined.

#[refine]
#[export]
Instance SETOID_cotriple
  {X : Setoid'} (h1 : SetoidHom A X) (h2 : SetoidHom B X) (Heq : forall x, h1 (f x) == h2 (g x))
  : SetoidHom SETOID_pushout X :=
{
  func := fun ab =>
    match ab with
    | inl a => h1 a
    | inr b => h2 b
    end;
}.
Proof.
  intros x y H; cbn in *.
  induction H as [z | x' y' Hglue | x' y' H IH | x' y' z' H1 IH1 H2 IH2].
  - now apply Heq.
  - destruct x' as [a1 | b1], y' as [a2 | b2]; cbn in *; try easy.
    + now rewrite Hglue.
    + now rewrite Hglue.
  - now rewrite IH.
  - now rewrite IH1, IH2.
Defined.

End Pushout.

#[refine]
#[export]
Instance HasPushouts_SETOID : HasPushouts SETOID :=
{
  pushout := @SETOID_pushout;
  pushl := @SETOID_pushl;
  pushr := @SETOID_pushr;
  cotriple := @SETOID_cotriple;
}.
Proof.
  split; cbn.
  - now constructor.
  - easy.
  - easy.
  - now intros Q h1 h2 HA HB [a | b].
Defined.
