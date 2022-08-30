From Cat Require Export Cat.
From Cat Require Import Category.CartesianClosed.
From Cat.Universal Require Export
  Initial Terminal Product Coproduct Equalizer Coequalizer Pullback Exponential
  IndexedProduct IndexedCoproduct.

#[refine]
#[export]
Instance CoqSet : Cat :=
{|
  Ob := Set;
  Hom := fun A B : Set => A -> B;
  HomSetoid := fun A B : Set => {| equiv := fun f g : A -> B => forall x : A, f x = g x |};
  comp := fun (A B C : Set) (f : A -> B) (g : B -> C) (a : A) => g (f a);
  id := fun (A : Set) (a : A) => a
|}.
Proof.
  (* Equivalence *) solve_equiv.
  (* Composition is proper *) proper. now rewrite H, H0.
  (* Category laws *) all: cat.
Defined.

Lemma CoqSet_isMono_inj :
  forall (A B : Ob CoqSet) (f : A -> B),
    isMono f <-> injective f.
Proof.
  unfold isMono, injective; cbn; split; intros.
  - now apply (H A (fun _ => x) (fun _ => y)).
  - apply H, H0.
Defined.

Lemma CoqSet_isRet_sur :
  forall (X Y : Set) (f : Hom X Y),
    isRet f <-> surjective f.
Proof.
  unfold isRet, surjective; cbn; split; intros.
    destruct H as [g eq]. exists (g b). apply eq.
    exists (
    fun y : Y => proj1_sig (constructive_indefinite_description _ (H y))).
      intro y. now destruct (constructive_indefinite_description _ (H y)).
Defined.

(* TODO : characterize epimorphisms and sections *)

Lemma CoqSet_isIso_bij :
  forall (A B : Set) (f : Hom A B),
    isIso f <-> bijective f.
Proof.
  split; intros.
    red. rewrite isIso_iff_isMono_isRet in H. destruct H. split.
      now rewrite <- CoqSet_isMono_inj.
      now rewrite <- CoqSet_isRet_sur.
    destruct H. rewrite isIso_iff_isMono_isRet. split.
      now rewrite CoqSet_isMono_inj.
      now rewrite CoqSet_isRet_sur.
Defined.

#[refine]
#[export]
Instance HasInit_CoqSet : HasInit CoqSet :=
{
  init := Empty_set;
  create := fun (X : Set) (e : Empty_set) => match e with end
}.
Proof. red; cat. Defined.

#[refine]
#[export]
Instance HasTerm_CoqSet : HasTerm CoqSet :=
{
  term := unit;
  delete := fun (X : Set) (x : X) => tt
}.
Proof. red; cat. Defined.

Definition isSingleton (A : Set) : Prop :=
  exists a : A, True /\ forall x y : A, x = y.

Definition isSingleton_delete :
  forall A : Set, isSingleton A -> forall X : Set, X -> A.
Proof.
  unfold isSingleton. intros.
  apply constructive_indefinite_description in H.
  destruct H as [a [_ H]]. exact a.
Defined.

Lemma isTerminal_CoqSet :
  forall (A : Set) (H : isSingleton A),
    @isTerminal CoqSet A (isSingleton_delete A H).
Proof.
  unfold isSingleton, isTerminal; intros; cat.
Qed.

Definition CoqSet_fpair (X Y A : Set) (f : Hom A X) (g : Hom A Y) : Hom A (prod X Y) :=
  fun x : A => (f x, g x).

#[refine]
#[export]
Instance HasProducts_CoqSet : HasProducts CoqSet :=
{
  product := prod;
  outl := @fst;
  outr := @snd;
  fpair := CoqSet_fpair
}.
Proof.
  split; unfold CoqSet_fpair; cbn; [easy | easy |].
  intros X f g Heq1 Heq2 x.
  now apply injective_projections.
Defined.

(* Beware! Requires functional extensionality. *)
#[refine]
#[export]
Instance HasIndexedProducts_CoqSet : HasIndexedProducts CoqSet :=
{
  indexedProduct := fun (J : Set) (A : J -> Ob CoqSet) => forall j : J, A j;
  proj := fun (J : Set) (A : J -> Ob CoqSet) (j : J) => fun (f : forall j : J, A j) => f j;
  tuple :=
    fun (J : Set) (A : J -> Ob CoqSet) (X : Ob CoqSet)
        (f : forall j : J, Hom X (A j)) (x : X) (j : J) => f j x
}.
Proof.
  split; cat.
  now extensionality a.
Defined.

Definition CoqSet_coproduct := sum.
Definition CoqSet_finl := @inl.
Definition CoqSet_finr := @inr.

Definition CoqSet_copair (X Y A : Set) (f : Hom X A) (g : Hom Y A) : Hom (sum X Y) A :=
  fun p : X + Y =>
  match p with
  | inl x => f x
  | inr y => g y
  end.

#[refine]
#[export]
Instance HasCoproducts_CoqSet : HasCoproducts CoqSet :=
{
  coproduct := sum;
  finl := @inl;
  finr := @inr;
  copair := CoqSet_copair
}.
Proof.
  split; cat.
  now destruct x.
Defined.

#[refine]
#[export]
Instance HasIndexedCoproducts_CoqSet : HasIndexedCoproducts CoqSet :=
{
  indexedCoproduct := fun (J : Set) (A : J -> Ob CoqSet) => {j : J & A j};
  coproj := fun (J : Set) (A : J -> Ob CoqSet) (j : J) => fun (x : A j) => existT A j x;
  cotuple :=
    fun (J : Set) (A : J -> Ob CoqSet) (X : Ob CoqSet)
      (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) =>
        f (projT1 p) (projT2 p)
}.
Proof.
  split; cat.
Defined.

Lemma CoqSet_counterexample1 :
  exists (A B C : Set) (f : Hom A B) (g : Hom B C),
    injective (f .> g) /\ ~ injective g.
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold injective, not; cbn; split; intros.
    now destruct x, y.
    now specialize (H true false eq_refl).
Qed.

Lemma CoqSet_counterexample2 :
  exists (A B C : Set) (f : Hom A B) (g : Hom B C),
    surjective (f .> g) /\ ~ surjective f.
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold surjective, not; cbn; split; intros.
    exists tt. now destruct b.
    destruct (H false). inversion H0.
Qed.

Definition CoqSet_equalizer {X Y : Set} (f g : X -> Y) : Set :=
  {x : X | f x = g x}.

Definition CoqSet_equalize {X Y : Set} (f g : X -> Y)
  (p : {x : X | f x = g x}) : X := proj1_sig p.

Definition CoqSet_factorize
  (X Y : Set) (f g : X -> Y)
  (E' : Set ) (e' : E' -> X) (H : forall x : E', f (e' x) = g (e' x))
  : E' -> {x : X | f x = g x}.
Proof.
 intro x. exists (e' x). apply H.
Defined.

#[refine]
#[export]
Instance HasEqualizers_CoqSet : HasEqualizers CoqSet :=
{
  equalizer := fun (X Y : Ob CoqSet) (f g : Hom X Y) => {x : X | f x = g x};
  equalize := fun (X Y : Ob CoqSet) (f g : Hom X Y) => fun (x : {x : X | f x = g x}) => proj1_sig x;
  factorize := @CoqSet_factorize;
}.
Proof.
  split; cbn.
  - now intros []; cbn.
  - easy.
  - intros. specialize (H x). destruct (e1 x), (e2 x); cbn in *.
    f_equal.
Abort.

#[refine]
#[export]
Instance HasExponentials_CoqSet : HasExponentials CoqSet :=
{
  expOb := fun X Y : Set => X -> Y;
  eval := fun (X Y : Set) (fx : product (X -> Y) X) => (fst fx) (snd fx);
  curry := fun (X Y Z : Set) (f : Z * X -> Y) (z : Z) => fun x : X => f (z, x)
}.
Proof.
  split; cbn.
  - intuition.
  - intros E' f g H x. extensionality a. apply (H (x, a)).
Defined.

#[export]
Instance CoqSet_CartesianClosed : CartesianClosed CoqSet :=
{
  HasTerm_CartesianClosed := HasTerm_CoqSet;
  HasProducts_CartesianClosed := HasProducts_CoqSet;
  HasExponentials_CartesianClosed := HasExponentials_CoqSet;
}.

Definition CoqSet_pullback {X Y A : Set} (f : X -> A) (g : Y -> A) : Set :=
  {p : X * Y | f (fst p) = g (snd p)}.

Definition CoqSet_pullL
  {X Y A : Set} (f : X -> A) (g : Y -> A) (p : CoqSet_pullback f g)
  : X := fst (proj1_sig p).

Definition CoqSet_pullR
  {X Y A : Set} (f : X -> A) (g : Y -> A) (p : CoqSet_pullback f g)
  : Y := snd (proj1_sig p).

Definition CoqSet_factor
  {X Y A : Set} (f : X -> A) (g : Y -> A) (P : Set) (p1 : P -> X) (p2 : P -> Y)
  : P -> CoqSet_pullback f g.
Proof.
  intro x. red. exists (p1 x, p2 x).
Abort.

#[refine]
#[export]
Instance HasPullbacks_CoqSet : HasPullbacks CoqSet :=
{
  pullback := @CoqSet_pullback;
  pullL := @CoqSet_pullL;
  pullR := @CoqSet_pullR;
}.
Proof.
Abort.