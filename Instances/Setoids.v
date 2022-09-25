From Cat Require Export Cat.
From Cat Require Import Category.CartesianClosed.
From Cat.Universal Require Export
  Initial Terminal Product Coproduct Equalizer Coequalizer Exponential IndexedProduct IndexedCoproduct.

Set Implicit Arguments.

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

Lemma CoqSetoid_surjectiveS :
  forall (X Y : Ob CoqSetoid) (f : Hom X Y),
    isEpi f -> surjectiveS f.
Proof.
  unfold isEpi, surjectiveS.
  cbn; intros X Y f HEpi y.
  pose (g := (fun y => exists a : X, f a == y) : Y -> PROP).
  assert (Proper_g : Proper (equiv ==> equiv) g)
    by now intros y1 y2 Heq; unfold g; cbn; setoid_rewrite Heq.
  pose (h := (fun _ : Y => True) : Y -> PROP).
  assert (Proper_h : Proper (equiv ==> equiv) h)
    by firstorder.
  pose (g' := {| func := g; Proper_func := Proper_g; |}).
  pose (h' := {| func := h; Proper_func := Proper_h; |}).
  specialize (HEpi PROP g' h').
  unfold g', g, h', h in HEpi; cbn in HEpi.
  rewrite HEpi; [easy |].
  now intuition eexists.
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

#[export]
Instance CoqSetoid_init : Setoid' :=
{
  carrier := Empty_set;
  setoid := Setoid_Empty;
}.

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

#[export]
Instance CoqSetoid_term : Setoid' :=
{
  carrier := unit;
  setoid := Setoid_unit;
}.

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

#[export]
Instance CoqSetoid_product (X Y : Setoid') : Setoid' :=
{
  carrier := X * Y;
  setoid := Setoid_prod X Y;
}.

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

#[export]
Instance CoqSetoid_coproduct (X Y : Setoid') : Setoid' :=
{
  carrier := sum X Y;
  setoid := Setoid_sum X Y;
}.

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

#[export]
Instance CoqSetoid_equalizer {X Y : Setoid'} (f g : SetoidHom X Y) : Setoid' :=
{
  carrier := {x : X | f x == g x};
  setoid := Setoid_sig X;
}.

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
| coeq_step : forall y y' : Y, y == y' -> CoqSetoid_coeq_equiv f g y y'
| coeq_quot : forall x : X, CoqSetoid_coeq_equiv f g (f x) (g x)
| coeq_sym  :
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

#[export]
Instance CoqSetoid_indexedProduct {J : Type} (A : J -> Setoid') : Setoid' :=
{
  carrier := forall j : J, A j;
  setoid := Setoid_forall A;
}.

#[export]
Instance CoqSetoid_out
  {J : Type} (A : J -> Setoid') (j : J) : SetoidHom (CoqSetoid_indexedProduct A) (A j).
Proof.
  exists (fun (f : forall j : J, A j) => f j).
  now proper.
Defined.

#[export]
Instance CoqSetoid_tuple
  {J : Type} {A : J -> Setoid'} {X : Setoid'}
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

#[export]
Instance CoqSetoid_indexedCoproduct {J : Type} (A : J -> Setoid') : Setoid' :=
{
  carrier := {j : J & A j};
  setoid := Setoid_sigT A;
}.

#[refine]
#[export]
Instance CoqSetoid_inj
  {J : Type} (A : J -> Setoid') (j : J) : SetoidHom (A j) (CoqSetoid_indexedCoproduct A) :=
{
  func := fun x : A j => existT _ j x
}.
Proof.
  now intros a1 a2 Heq; cbn; exists eq_refl.
Defined.

#[refine]
#[export]
Instance CoqSetoid_cotuple
  {J : Type} {A : J -> Setoid'} {X : Setoid'}
  (f : forall j : J, SetoidHom (A j) X)
  : SetoidHom (CoqSetoid_indexedCoproduct A) X :=
{
  func := fun x => f (projT1 x) (projT2 x)
}.
Proof.
  now intros [x x'] [y y']; cbn; intros [-> ->].
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
  split; cbn.
  - easy.
  - now intros X h1 h2 Heq [x x'].
Defined.

#[export]
Instance CoqSetoid_exponential (X Y : Setoid') : Setoid' :=
{
  carrier := SetoidHom X Y;
  setoid := Setoid_SetoidHom X Y;
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

(** nel-related stuff *)

#[export]
Instance CoqSetoid_sumprod (A B : Setoid') : Setoid' :=
{
  carrier := sumprod A B;
  setoid := Setoid_sumprod A B;
}.

#[refine]
#[export]
Instance CoqSetoid_inl' (A B : Setoid') : SetoidHom A (CoqSetoid_sumprod A B) :=
{
  func := @inl' A B;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance CoqSetoid_inr' (A B : Setoid') : SetoidHom B (CoqSetoid_sumprod A B) :=
{
  func := @inr' A B;
}.
Proof. easy. Defined.

#[export]
Instance CoqSetoid_nel (X : Setoid') : Setoid' :=
{
  carrier := nel X;
}.