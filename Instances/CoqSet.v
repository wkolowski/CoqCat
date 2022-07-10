From Cat Require Export Cat.
From Cat Require Import Category.CartesianClosed.
From Cat.Limits Require Export InitTerm BinProdCoprod BigProdCoprod Equalizer Pullback Exponential.

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

Lemma CoqSet_mon_inj :
  forall (A B : Ob CoqSet) (f : A -> B),
    Mon f <-> injective f.
Proof.
  unfold Mon, injective; cbn; split; intros.
    change (x = y) with ((fun _ => x) x = (fun _ => y) x).
      apply H. auto.
    apply H. apply H0.
Defined.

Lemma CoqSet_ret_sur :
  forall (X Y : Set) (f : Hom X Y),
    Ret f <-> surjective f.
Proof.
  unfold Ret, surjective; cbn; split; intros.
    destruct H as [g eq]. exists (g b). apply eq.
    exists (
    fun y : Y => proj1_sig (constructive_indefinite_description _ (H y))).
      intro y. destruct (constructive_indefinite_description _ (H y)).
      simpl. assumption.
Defined.

(* TODO : characterize epimorphisms and sections *)

Lemma CoqSet_iso_bij :
  forall (A B : Set) (f : Hom A B),
    Iso f <-> bijective f.
Proof.
  split; intros.
    red. rewrite iso_iff_mon_ret in H. destruct H. split.
      rewrite <- CoqSet_mon_inj. assumption.
      rewrite <- CoqSet_ret_sur. assumption.
    destruct H. rewrite iso_iff_mon_ret. split.
      rewrite CoqSet_mon_inj. assumption.
      rewrite CoqSet_ret_sur. assumption.
Defined.

#[refine]
#[export]
Instance CoqSet_HasInit : HasInit CoqSet :=
{
  init := Empty_set;
  create := fun (X : Set) (e : Empty_set) => match e with end
}.
Proof. cat. Defined.

#[refine]
#[export]
Instance CoqSet_HasTerm : HasTerm CoqSet :=
{
  term := unit;
  delete := fun (X : Set) (x : X) => tt
}.
Proof. cat. Defined.

Definition is_singleton (A : Set) : Prop :=
  exists a : A, True /\ forall (x y : A), x = y.

Definition is_singleton_delete :
  forall A : Set, is_singleton A -> forall X : Set, X -> A.
Proof.
  unfold is_singleton. intros.
  apply constructive_indefinite_description in H.
  destruct H as [a [_ H]]. exact a.
Defined.

Lemma CoqSet_terminal_ob :
  forall (A : Set) (H : is_singleton A),
    @terminal CoqSet A (is_singleton_delete A H).
Proof.
  unfold is_singleton, terminal; intros. cat.
  compute. destruct (constructive_indefinite_description _ _).
  destruct a. erewrite e. reflexivity.
Qed.

Definition CoqSet_fpair (X Y A : Set) (f : Hom A X) (g : Hom A Y) : Hom A (prod X Y) :=
  fun x : A => (f x, g x).

#[refine]
#[export]
Instance CoqSet_HasProducts : HasProducts CoqSet :=
{
  prodOb := prod;
  proj1 := @fst;
  proj2 := @snd;
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
Instance CoqSet_HasAllProducts : HasAllProducts CoqSet :=
{
  bigProdOb := fun (J : Set) (A : J -> Ob CoqSet) => forall j : J, A j;
  bigProj := fun (J : Set) (A : J -> Ob CoqSet) (j : J) => fun (f : forall j : J, A j) => f j;
  tuple :=
    fun (J : Set) (A : J -> Ob CoqSet) (X : Ob CoqSet)
        (f : forall j : J, Hom X (A j)) (x : X) (j : J) => f j x
}.
Proof.
  (* Proper *) cat. extensionality j. auto.
  (* Universal property *) red; cat. extensionality a. auto.
Defined.

Definition CoqSet_coprodOb := sum.
Definition CoqSet_coproj1 := @inl.
Definition CoqSet_coproj2 := @inr.

Definition CoqSet_copair (X Y A : Set) (f : Hom X A) (g : Hom Y A) : Hom (sum X Y) A :=
  fun p : X + Y =>
  match p with
  | inl x => f x
  | inr y => g y
  end.

#[refine]
#[export]
Instance CoqSet_HasCoproducts : HasCoproducts CoqSet :=
{
  coprodOb := sum;
  coproj1 := @inl;
  coproj2 := @inr;
  copair := CoqSet_copair
}.
Proof.
  all: repeat red; cat;
  match goal with | x : _ + _ |- _ => destruct x end; cat.
Defined.

#[refine]
#[export]
Instance CoqSet_HasAllCoproducts : HasAllCoproducts CoqSet :=
{
  bigCoprodOb := fun (J : Set) (A : J -> Ob CoqSet) => {j : J & A j};
  bigCoproj := fun (J : Set) (A : J -> Ob CoqSet) (j : J) => fun (x : A j) => existT A j x;
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
Instance CoqSet_HasEqualizers : HasEqualizers CoqSet :=
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
  - cbn; intros X Y f f' g g' Hf Hg.
    assert ({x : X | f x = g x} = {x : X | f' x = g' x}).
    + f_equal. extensionality x. rewrite Hf, Hg. reflexivity.
    +
Abort.

#[refine]
#[export]
Instance CoqSet_HasEqualizers' : HasEqualizers CoqSet :=
{
  eq_ob := fun (X Y : Ob CoqSet) (f g : Hom X Y) => {x : X | f x = g x};
  eq_mor := fun (X Y : Ob CoqSet) (f g : Hom X Y) => fun (x : {x : X | f x = g x}) => proj1_sig x;
  factorize := @CoqSet_factorize;
}.
Proof.
  intros. cbn in *. assert ({x : X | f x = g x} = {x : X | f' x = g' x}).
    f_equal. extensionality x. rewrite H, H0. trivial.
    rewrite H1 in *. constructor. reflexivity.
  intros. cbn in *. assert ({x : X | f x = g x} = {x : X | f' x = g' x}).
    f_equal. extensionality x. rewrite H, H0. trivial.
    assert (JMeq (fun x : {x : X | f x = g x} => proj1_sig x)
      (fun x : {x : X | f' x = g' x} => proj1_sig x)).
Abort.

#[refine]
#[export]
Instance CoqSet_HasCoequalizers : HasCoequalizers CoqSet := {}.
Proof.
Abort.

#[refine]
#[export]
Instance CoqSet_HasExponentials : HasExponentials CoqSet :=
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
Instance CoqSet_cartesian_closed : cartesian_closed CoqSet :=
{
  ccc_term := CoqSet_HasTerm;
  ccc_prod := CoqSet_HasProducts;
  ccc_exp := CoqSet_HasExponentials;
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
Instance CoqSet_HasPullbacks : HasPullbacks CoqSet :=
{
  pullbackOb := @CoqSet_pullbackOb;
  pull1 := @CoqSet_pull1;
  pull2 := @CoqSet_pull2;
}.
Proof.
Abort.