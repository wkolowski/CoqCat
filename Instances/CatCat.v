Require Import Cat.
Require Import Cat.Functor.

Require Import Limits.InitTerm.
Require Import Limits.BinProdCoprod.

Require Import Instances.Discrete.

Require Import FunctionalExtensionality.

Require Import Eqdep.

Set Implicit Arguments.

#[refine]
Instance CAT : Cat :=
{
    Ob := Cat;
    Hom := Functor;
    HomSetoid := fun C D : Cat =>
      {| equiv := fun T S : Functor C D =>
        depExtEq (fob T) (fob S) /\ depExtEq (fmap T) (fmap S) |};
    (*HomSetoid := fun C D : Cat =>
      {| equiv := fun T S : Functor C D =>
        JMeq (fob T) (fob S) /\ JMeq (fmap T) (fmap S) |};*)
    comp := @FunctorComp;
    id := FunctorId
}.
Proof.
  (* Equivalence *) solve_equiv. (*
    rewrite H, H0. reflexivity.
    rewrite H2, H1. reflexivity.
  all: cat.
    rewrite H, H0. reflexivity.
    rewrite H2. reflexivity.*)
  

  (* Proper *) proper. my_simpl; solve_depExtEq.
  (* Category laws *) all: cat.
Defined.

Instance CAT_init : Cat := Discrete Empty_set.

#[refine]
Instance CAT_create (X : Cat) : Functor CAT_init X :=
{
    fob := fun e => match e with end;
    fmap := fun e _ _ => match e with end
}.
Proof. all: cat. Defined.

#[refine]
Instance CAT_has_init : has_init CAT :=
{
    init := CAT_init;
    create := CAT_create
}.
Proof.
  cbn. split.
    apply depExtEq_ext. destruct x.
    apply depExtEq_ext. destruct x.
Defined.

Instance CAT_term : Cat := Discrete unit.

#[refine]
Instance CAT_delete (X : Cat) : Functor X CAT_term :=
{
    fob := fun _ => tt;
}.
Proof. all: cat. Defined.

#[refine]
Instance CAT_has_term : has_term CAT :=
{
    term := CAT_term;
    delete := CAT_delete;
}.
Proof.
  cbn. split; solve_depExtEq.
    destruct (fob f x). reflexivity.
    destruct (fmap f x1). cat.
Defined.

#[refine]
Instance CAT_proj1 (X Y : Cat) : Functor (CAT_prodOb X Y) X :=
{
    fob := fst;
    fmap := fun _ _ => fst
}.
Proof. all: cat. Defined.

#[refine]
Instance CAT_proj2 (X Y : Cat) : Functor (CAT_prodOb X Y) Y :=
{
    fob := snd;
    fmap := fun _ _ => snd
}.
Proof. all: cat. Defined.

#[refine]
Instance CAT_fpair (X Y A : Cat) (F : Functor A X) (G : Functor A Y)
  : Functor A (CAT_prodOb X Y) :=
{
    fob := fun X : Ob A => (fob F X, fob G X);
    fmap := fun _ _ f => (fmap F f, fmap G f)
}.
Proof. all: cat; functor. Defined.

#[refine]
Instance CAT_has_products : has_products CAT :=
{
    prodOb := CAT_prodOb;
    proj1 := CAT_proj1;
    proj2 := CAT_proj2;
    fpair := CAT_fpair
}.
Proof.
  proper. destruct H, H0. split.
    solve_depExtEq.
    do 3 (apply depExtEq_ext; intro).
      apply (depExtEq_unext (pair _) (pair _)).
        apply (depExtEq_unext pair pair).
          solve_depExtEq.
        solve_depExtEq.
      solve_depExtEq.
  unfold product_skolem. repeat split; solve_depExtEq.
  all: cbn in *; my_simpl.
Abort.