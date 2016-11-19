Add LoadPath "/home/zeimer/Code/Coq/CoqCat/New".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export FunctionalExtensionality.

Set Universe Polymorphism.

Instance SetP : Cat.
refine
{|
  Ob := Set;
  Hom := fun A B : Set => A -> option B;
  comp := fun (A B C : Set) (f : A -> option B) (g : B -> option C) =>
    fun a : A => match f a with
        | None => None
        | Some b => g b
    end;
  id := Some
|}; simpl; cat;
extensionality x; destruct (f x); try destruct (g b); auto.
Defined.
Print initial.

Theorem has_initial : @initial SetP Empty_set.
Proof.
  red. intro. exists (fun x : Empty_set => match x with end).
  split; intros; auto. extensionality a. destruct a.
Qed.

Theorem has_terminal : @terminal SetP Empty_set.
Proof.
  red. intro A. exists (fun x : A => None).
  split; intros; auto. extensionality a. destruct (x' a); intuition.
Qed.

Hint Unfold initial terminal zero_object.
Hint Resolve has_initial has_terminal.

Theorem has_zero : @zero_object SetP Empty_set.
Proof. auto. Qed.
    
