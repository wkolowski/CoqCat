Add LoadPath "/home/zeimer/Code/Coq/CoqCat/New".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export FunctionalExtensionality.
Require Import ClassicalFacts.

Set Universe Polymorphism.

Class Sgr : Type :=
{
    carrier : Type;
    op : carrier -> carrier -> carrier;
    assoc : forall x y z : carrier, op x (op y z) = op (op x y) z
}.

Coercion carrier : Sgr >-> Sortclass.

Definition SgrHom (A B : Sgr) : Type :=
    {f : A -> B | forall x y : A, f (op x y) = op (f x) (f y)}.

Definition SgrComp (A B C : Sgr) (f : SgrHom A B) (g : SgrHom B C)
    : SgrHom A C.
Proof.
  red. destruct f as [f Hf], g as [g Hg].
  exists (fun a : A => g (f a)). intros. rewrite Hf, Hg. trivial.
Defined.

Definition SgrId (A : Sgr) : SgrHom A A.
Proof. red. exists (fun a : A => a). auto. Defined.

Instance CatSgr : Cat.
refine
{|
    Ob := Sgr;
    Hom := SgrHom;
    comp := SgrComp;
    id := SgrId
|}.
Proof.
  intros. unfold SgrComp. destruct f, g, h. f_equal.
  extensionality a. extensionality b. destruct A, B, C, D.
Abort.

Class SgrHom' (A B : Sgr) : Type :=
{
    f : A -> B;
    property : forall x y : A, f (op x y) = op (f x) (f y)
}.

Instance CatSgr' : Cat :=
{
    Ob := Sgr;
    Hom := SgrHom'
}.
Proof.
  destruct 1 as [f Hf], 1 as [g Hg]. split with (fun a : A => g (f a)).
    intros. rewrite Hf, Hg. reflexivity.
  intro. split with (f := fun a : A => a). auto.
  unfold Hom, SgrHom, comp, SgrComp, id, SgrId.
  intros. destruct f0, g, h. f_equal. extensionality a;
    extensionality b. destruct A, B, C, D. compute.
    apply proof_irrelevance.