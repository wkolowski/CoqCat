From Stdlib Require Import FunctionalExtensionality PropExtensionality.
From Cat Require Export Cat.
From Cat Require Import Category.CartesianClosed.
From Cat.Universal Require Export
  Initial Terminal Product Coproduct Equalizer Coequalizer Pullback Exponential
  IndexedProduct IndexedCoproduct.

#[refine]
#[export]
Instance SET : Cat :=
{|
  Ob := Type;
  Hom := fun A B : Type => A -> B;
  HomSetoid := fun A B : Type => {| equiv := fun f g : A -> B => forall x : A, f x = g x |};
  comp := fun (A B C : Type) (f : A -> B) (g : B -> C) (a : A) => g (f a);
  id := fun (A : Type) (a : A) => a
|}.
Proof.
  - now solve_equiv.
  - now proper; congruence.
  - easy.
  - easy.
  - easy.
Defined.

Lemma SET_isMono :
  forall (A B : Ob SET) (f : A -> B),
    isMono f <-> injective f.
Proof.
  unfold isMono, injective; cbn.
  split; intros.
  - now apply (H A (fun _ => x) (fun _ => y)).
  - now apply H, H0.
Defined.

Lemma SET_isEpi :
  forall (X Y : Type) (f : Hom X Y),
    isEpi f <-> surjective f.
Proof.
  unfold isEpi, surjective; cbn.
  split; cycle 1.
  - intros Hsur Z h1 h2 Heq y.
    destruct (Hsur y) as [x <-].
    now apply Heq.
  - intros HEpi y.
    pose (g := fun y => exists a : X, f a = y).
    pose (h := fun _ : Y => True).
    specialize (HEpi Prop g h).
    unfold g, h in HEpi.
    rewrite HEpi; [easy |].
    intros x.
    now apply propositional_extensionality; intuition eauto.
Qed.

#[refine]
#[export]
Instance HasInit_SET : HasInit SET :=
{
  init := Empty_set;
  create := fun (X : Type) (e : Empty_set) => match e with end
}.
Proof. easy. Defined.

#[export]
Instance HasStrictInit_SET : HasStrictInit SET.
Proof.
  intros A f.
  exists (create A).
  split; cycle 1.
  - now apply equiv_initial.
  - now intros x; destruct (f x).
Defined.

#[refine]
#[export]
Instance HasTerm_SET : HasTerm SET :=
{
  term := unit;
  delete := fun (X : Type) (x : X) => tt
}.
Proof.
  now intros A f g x; apply eq_unit_intro.
Defined.

Definition isSingleton (A : Type) : Type :=
  {a : A | forall x y : A, x = y}.

Definition isSingleton_delete :
  forall A : Type, isSingleton A -> forall X : Type, X -> A.
Proof.
  unfold isSingleton.
  intros A (a & H) X x.
  exact a.
Defined.

Lemma isTerminal_SET :
  forall (A : Type) (H : isSingleton A),
    @isTerminal SET A (isSingleton_delete A H).
Proof.
  now red; firstorder.
Qed.

Definition SET_fpair (X Y A : Type) (f : Hom A X) (g : Hom A Y) : Hom A (prod X Y) :=
  fun x : A => (f x, g x).

#[refine]
#[export]
Instance HasProducts_SET : HasProducts SET :=
{
  product := prod;
  outl := @fst;
  outr := @snd;
  fpair := SET_fpair
}.
Proof.
  split; unfold SET_fpair; cbn; [easy | easy |].
  intros X f g Heq1 Heq2 x.
  now apply injective_projections.
Defined.

(* Beware! Requires functional extensionality. *)
#[refine]
#[export]
Instance HasIndexedProducts_SET : HasIndexedProducts SET :=
{
  indexedProduct := fun (J : Type) (A : J -> Ob SET) => forall j : J, A j;
  out := fun (J : Type) (A : J -> Ob SET) (j : J) => fun (f : forall j : J, A j) => f j;
  tuple :=
    fun (J : Type) (A : J -> Ob SET) (X : Ob SET)
        (f : forall j : J, Hom X (A j)) (x : X) (j : J) => f j x
}.
Proof.
  split; cbn; intros.
  - easy.
  - now extensionality j.
Defined.

Definition SET_coproduct := sum.
Definition SET_finl := @inl.
Definition SET_finr := @inr.

Definition SET_copair (X Y A : Type) (f : Hom X A) (g : Hom Y A) : Hom (sum X Y) A :=
  fun p : X + Y =>
  match p with
  | inl x => f x
  | inr y => g y
  end.

#[refine]
#[export]
Instance HasCoproducts_SET : HasCoproducts SET :=
{
  coproduct := sum;
  finl := @inl;
  finr := @inr;
  copair := SET_copair
}.
Proof.
  split; cbn; [easy | easy |].
  now intros P' h1 h2 HeqA heqB [a | b].
Defined.

#[refine]
#[export]
Instance HasIndexedCoproducts_SET : HasIndexedCoproducts SET :=
{
  indexedCoproduct := fun (J : Type) (A : J -> Ob SET) => {j : J & A j};
  inj := fun (J : Type) (A : J -> Ob SET) (j : J) => fun (x : A j) => existT A j x;
  cotuple :=
    fun (J : Type) (A : J -> Ob SET) (X : Ob SET)
      (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) =>
        f (projT1 p) (projT2 p)
}.
Proof.
  split; cbn.
  - easy.
  - intros X h1 h2 Heq [j a].
    now apply Heq.
Defined.

Lemma SET_counterexample1 :
  exists (A B C : Type) (f : Hom A B) (g : Hom B C),
    injective (f .> g) /\ ~ injective g.
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold injective, not; cbn; split; intros.
  - now destruct x, y.
  - now specialize (H true false eq_refl).
Qed.

Lemma SET_counterexample2 :
  exists (A B C : Type) (f : Hom A B) (g : Hom B C),
    surjective (f .> g) /\ ~ surjective f.
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold surjective, not; cbn; split; intros.
  - exists tt. now destruct b.
  - destruct (H false). inversion H0.
Qed.

Definition SET_equalizer {X Y : Type} (f g : X -> Y) : Type :=
  {x : X | f x = g x}.

Definition SET_equalize {X Y : Type} (f g : X -> Y)
  (p : {x : X | f x = g x}) : X := proj1_sig p.

Definition SET_factorize
  (X Y : Type) (f g : X -> Y)
  (E' : Type) (e' : E' -> X) (H : forall x : E', f (e' x) = g (e' x))
  : E' -> {x : X | f x = g x}
  := fun x : E' => exist _ (e' x) (H x).

#[refine]
#[export]
Instance HasEqualizers_SET : HasEqualizers SET :=
{
  equalizer := fun (X Y : Ob SET) (f g : Hom X Y) => {x : X | f x = g x};
  equalize := fun (X Y : Ob SET) (f g : Hom X Y) => fun (x : {x : X | f x = g x}) => proj1_sig x;
  factorize := @SET_factorize;
}.
Proof.
  split; cbn.
  - now intros []; cbn.
  - easy.
  - intros E' e1 e2 Heq x.
    specialize (Heq x).
    destruct (e1 x), (e2 x); cbn in *.
Abort.

#[refine]
#[export]
Instance HasExponentials_SET : HasExponentials SET :=
{
  exponential := fun X Y : Type => X -> Y;
  eval := fun (X Y : Type) (fx : product (X -> Y) X) => (fst fx) (snd fx);
  curry := fun (X Y Z : Type) (f : Z * X -> Y) (z : Z) => fun x : X => f (z, x)
}.
Proof.
  split; cbn.
  - now intros E' f [].
  - intros E' f g H x.
    extensionality a.
    now apply (H (x, a)).
Defined.

#[export]
Instance SET_CartesianClosed : CartesianClosed SET :=
{
  HasTerm_CartesianClosed := HasTerm_SET;
  HasProducts_CartesianClosed := HasProducts_SET;
  HasExponentials_CartesianClosed := HasExponentials_SET;
}.

Definition SET_pullback
  {A B X : Type} (f : A -> X) (g : B -> X) : Type :=
    {p : A * B | f (fst p) = g (snd p)}.

Definition SET_pullL
  {A B X : Type} (f : A -> X) (g : B -> X)
  : SET_pullback f g -> A
  := fun p => fst (proj1_sig p).

Definition SET_pullR
  {A B X : Type} (f : A -> X) (g : B -> X)
  : SET_pullback f g -> B
  := fun p => snd (proj1_sig p).

Definition SET_triple
  {A B X : Type} (f : A -> X) (g : B -> X)
  (Γ : Type) (a : Γ -> A) (b : Γ -> B) (Heq : forall x : Γ, f (a x) = g (b x))
  : Γ -> SET_pullback f g
  := fun x => exist _ (a x, b x) (Heq x).

#[refine]
#[export]
Instance HasPullbacks_SET : HasPullbacks SET :=
{
  pullback := @SET_pullback;
  pullL := @SET_pullL;
  pullR := @SET_pullR;
  triple := @SET_triple;
}.
Proof.
  split; cbn.
  - now intros [[a b] H]; cbn in *.
  - easy.
  - easy.
  - intros Γ h1 h2 Hl Hr x.
    specialize (Hl x); specialize (Hr x).
    destruct (h1 x) as [[a1 b1] H1], (h2 x) as [[a2 b2] H2]; cbn in *.
Abort.
