From Cat Require Export Cat.
From Cat Require Import Category.CartesianClosed.
From Cat.Limits Require Export InitTerm Product Coproduct IndexedProduct IndexedCoproduct Equalizer Coequalizer Pullback Exponential.

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
  (* Composition is proper *) proper. rewrite H, H0. auto.
  (* Category laws *) all: cat.
Defined.

Lemma CoqSet_isMono_inj :
  forall (A B : Ob CoqSet) (f : A -> B),
    isMono f <-> injective f.
Proof.
  unfold isMono, injective; cbn; split; intros.
    change (x = y) with ((fun _ => x) x = (fun _ => y) x).
      apply H. auto.
    apply H. apply H0.
Defined.

Lemma CoqSet_isRet_sur :
  forall (X Y : Set) (f : Hom X Y),
    isRet f <-> surjective f.
Proof.
  unfold isRet, surjective; cbn; split; intros.
    destruct H as [g eq]. exists (g b). apply eq.
    exists (
    fun y : Y => proj1_sig (constructive_indefinite_description _ (H y))).
      intro y. destruct (constructive_indefinite_description _ (H y)).
      simpl. assumption.
Defined.

(* TODO : characterize epimorphisms and sections *)

Lemma CoqSet_isIso_bij :
  forall (A B : Set) (f : Hom A B),
    isIso f <-> bijective f.
Proof.
  split; intros.
    red. rewrite isIso_iff_isMono_isRet in H. destruct H. split.
      rewrite <- CoqSet_isMono_inj. assumption.
      rewrite <- CoqSet_isRet_sur. assumption.
    destruct H. rewrite isIso_iff_isMono_isRet. split.
      rewrite CoqSet_isMono_inj. assumption.
      rewrite CoqSet_isRet_sur. assumption.
Defined.

#[refine]
#[export]
Instance HasInit_CoqSet : HasInit CoqSet :=
{
  init := Empty_set;
  create := fun (X : Set) (e : Empty_set) => match e with end
}.
Proof. cat. Defined.

#[refine]
#[export]
Instance HasTerm_CoqSet : HasTerm CoqSet :=
{
  term := unit;
  delete := fun (X : Set) (x : X) => tt
}.
Proof. cat. Defined.

Definition isSingleton (A : Set) : Prop :=
  exists a : A, True /\ forall x y : A, x = y.

Definition isSingleton_delete :
  forall A : Set, isSingleton A -> forall X : Set, X -> A.
Proof.
  unfold isSingleton. intros.
  apply constructive_indefinite_description in H.
  destruct H as [a [_ H]]. exact a.
Defined.

Lemma CoqSet_terminal_ob :
  forall (A : Set) (H : isSingleton A),
    @isTerminal CoqSet A (isSingleton_delete A H).
Proof.
  unfold isSingleton, isTerminal; intros. cat.
  compute. destruct (constructive_indefinite_description _ _).
  destruct a. erewrite e. reflexivity.
Qed.

Definition CoqSet_fpair (X Y A : Set) (f : Hom A X) (g : Hom A Y) : Hom A (prod X Y) :=
  fun x : A => (f x, g x).

#[refine]
#[export]
Instance HasProducts_CoqSet : HasProducts CoqSet :=
{
  prodOb := prod;
  outl := @fst;
  outr := @snd;
  fpair := CoqSet_fpair
}.
Proof.
  all: unfold CoqSet_fpair.
  (* Proper *) proper. rewrite H, H0. auto.
  (* Product law *) red; cat. rewrite H, H0. destruct (y x). auto.
Defined.

(* Beware! Requires functional extensionality. *)
#[refine]
#[export]
Instance HasIndexedProducts_CoqSet : HasIndexedProducts CoqSet :=
{
  indexedProdOb := fun (J : Set) (A : J -> Ob CoqSet) => forall j : J, A j;
  indexedProj := fun (J : Set) (A : J -> Ob CoqSet) (j : J) => fun (f : forall j : J, A j) => f j;
  tuple :=
    fun (J : Set) (A : J -> Ob CoqSet) (X : Ob CoqSet)
        (f : forall j : J, Hom X (A j)) (x : X) (j : J) => f j x
}.
Proof.
  (* Proper *) cat. extensionality j. auto.
  (* Universal property *) red; cat. extensionality a. auto.
Defined.

Definition CoqSet_coprodOb := sum.
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
  coprodOb := sum;
  finl := @inl;
  finr := @inr;
  copair := CoqSet_copair
}.
Proof.
  all: repeat red; cat;
  match goal with | x : _ + _ |- _ => destruct x end; cat.
Defined.

#[refine]
#[export]
Instance HasIndexedCoproducts_CoqSet : HasIndexedCoproducts CoqSet :=
{
  indexedCoprodOb := fun (J : Set) (A : J -> Ob CoqSet) => {j : J & A j};
  indexedCoproj := fun (J : Set) (A : J -> Ob CoqSet) (j : J) => fun (x : A j) => existT A j x;
  cotuple :=
    fun (J : Set) (A : J -> Ob CoqSet) (X : Ob CoqSet)
      (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) =>
        f (projT1 p) (projT2 p)
}.
Proof.
  all: try red; cat.
Defined.

Lemma CoqSet_counterexample1 :
  exists (A B C : Set) (f : Hom A B) (g : Hom B C),
    injective (f .> g) /\ ~ injective g.
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold injective, not; cbn; split; intros.
    destruct x, y; auto.
    specialize (H true false eq_refl). discriminate H.
Qed.

Lemma CoqSet_counterexample2 :
  exists (A B C : Set) (f : Hom A B) (g : Hom B C),
    surjective (f .> g) /\ ~ surjective f.
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold surjective, not; cbn; split; intros.
    exists tt. destruct b. auto.
    destruct (H false). inversion H0.
Qed.

Definition CoqSet_eq_ob {X Y : Set} (f g : X -> Y) : Set :=
  {x : X | f x = g x}.

Definition CoqSet_eq_mor {X Y : Set} (f g : X -> Y)
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
  eq_ob := fun (X Y : Ob CoqSet) (f g : Hom X Y) => {x : X | f x = g x};
  eq_mor := fun (X Y : Ob CoqSet) (f g : Hom X Y) =>
    fun (x : {x : X | f x = g x}) => proj1_sig x;
}.
Proof.
  - cbn; intros X Y f f' g g' Hf Hg.
    replace {x : X | f x = g x} with {x : X | f' x = g' x}.
    + constructor. cbn. reflexivity.
    + f_equal. extensionality x. rewrite Hf, Hg. reflexivity.
  - intros X Y f g [x Heq]; cbn. assumption.
  - cbn; intros X Y f f' g g' Hf Hg.
    assert ({x : X | f x = g x} = {x : X | f' x = g' x}).
    + f_equal. extensionality x. rewrite Hf, Hg. reflexivity.
    +
Abort.

#[refine]
#[export]
Instance HasEqualizers_CoqSet' : HasEqualizers CoqSet :=
{
  eq_ob := fun (X Y : Ob CoqSet) (f g : Hom X Y) => {x : X | f x = g x};
  eq_mor := fun (X Y : Ob CoqSet) (f g : Hom X Y) => fun (x : {x : X | f x = g x}) => proj1_sig x;
  factorize := @CoqSet_factorize;
}.
Proof.
  - intros. cbn in *.
    assert ({x : X | f x = g x} = {x : X | f' x = g' x}).
    {
      f_equal. extensionality x. rewrite H, H0. trivial.
    }
    rewrite H1 in *. constructor. reflexivity.
  - intros X Y f g [x Heq]; cbn. assumption.
  - intros. cbn in *.
    assert ({x : X | f x = g x} = {x : X | f' x = g' x}).
    {
      f_equal. extensionality x. rewrite H, H0. trivial.
    }
    assert (JMeq (fun x : {x : X | f x = g x} => proj1_sig x)
      (fun x : {x : X | f' x = g' x} => proj1_sig x)).
Abort.

#[refine]
#[export]
Instance HasCoequalizers_CoqSet : HasCoequalizers CoqSet := {}.
Proof.
Abort.

#[refine]
#[export]
Instance HasExponentials_CoqSet : HasExponentials CoqSet :=
{
  expOb := fun X Y : Set => X -> Y;
  eval := fun (X Y : Set) (fx : prodOb (X -> Y) X) => (fst fx) (snd fx);
  curry := fun (X Y Z : Set) (f : Z * X -> Y) (z : Z) => fun x : X => f (z, x)
}.
Proof.
  proper. extensionality a. rewrite H. reflexivity.
  do 2 red; cbn; split; intros.
    destruct x; cbn. reflexivity.
    extensionality x'. rewrite <- H. simpl. reflexivity.
Defined.

#[export]
Instance CoqSet_CartesianClosed : CartesianClosed CoqSet :=
{
  HasTerm_CartesianClosed := HasTerm_CoqSet;
  HasProducts_CartesianClosed := HasProducts_CoqSet;
  HasExponentials_CartesianClosed := HasExponentials_CoqSet;
}.

Definition CoqSet_pullbackOb {X Y A : Set} (f : X -> A) (g : Y -> A) : Set :=
  {p : X * Y | f (fst p) = g (snd p)}.

Definition CoqSet_pull1
  {X Y A : Set} (f : X -> A) (g : Y -> A) (p : CoqSet_pullbackOb f g)
  : X := fst (proj1_sig p).

Definition CoqSet_pull2
  {X Y A : Set} (f : X -> A) (g : Y -> A) (p : CoqSet_pullbackOb f g)
  : Y := snd (proj1_sig p).

Definition CoqSet_factor
  {X Y A : Set} (f : X -> A) (g : Y -> A) (P : Set) (p1 : P -> X) (p2 : P -> Y)
  : P -> CoqSet_pullbackOb f g.
Proof.
  intro x. red. exists (p1 x, p2 x).
Abort.

#[refine]
#[export]
Instance HasPullbacks_CoqSet : HasPullbacks CoqSet :=
{
  pullbackOb := @CoqSet_pullbackOb;
  pull1 := @CoqSet_pull1;
  pull2 := @CoqSet_pull2;
}.
Proof.
Abort.