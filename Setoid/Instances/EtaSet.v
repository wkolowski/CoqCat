Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Cat.
Require Export InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.
Require Import Equalizer.

Require Export Equivalences.

Instance EtaSet : Cat :=
{|
    Ob := Set;
    Hom := fun A B : Set => A -> B;
    HomSetoid := fun A B : Set =>
        {| equiv := @eta (A -> B) |};
    comp := fun (A B C : Set) (f : A -> B) (g : B -> C) (a : A) => g (f a);
    id := fun (A : Set) (a : A) => a
|}.
Proof.
  apply eta_Equivalence.
  (* Composition is proper *) unfold Proper, respectful. simpl. intros.
    destruct H.
  (* Category laws *) all:cat.
Defined.