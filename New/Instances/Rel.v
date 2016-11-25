Add LoadPath "/home/zeimer/Code/Coq/CoqCat/New".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export FunctionalExtensionality.
Require Import ClassicalFacts.

Set Universe Polymorphism.

Instance Rel : Cat.
refine
{|
    Ob := Set;
    Hom := fun A B : Set => A -> B -> Prop;
    comp := fun (A B C : Set) (R : A -> B -> Prop) (S : B -> C -> Prop) =>
        fun (a : A) (c : C) => exists b : B, R a b /\ S b c;
    id := fun (A : Set) => @eq A
|}.
Proof. Focus 2. intros. extensionality a. extensionality c.
  
  intros. extensionality a. extensionality d.
  apply prop_extensionality.