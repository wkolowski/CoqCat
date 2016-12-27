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

Inductive prodsum (A B : Set) : Set :=
    | inl' : A -> prodsum A B
    | inr' : B -> prodsum A B
    | pair' : A -> B -> prodsum A B.

Arguments inl' [A] [B] _.
Arguments inr' [A] [B] _.
Arguments pair' [A] [B] _ _.

Definition prodsum_proj1 {A B : Set} (x : prodsum A B) : option A :=
match x with
    | inl' a => Some a
    | pair' a _ => Some a
    | _ => None
end.

Definition prodsum_proj2 {A B : Set} (x : prodsum A B) : option B :=
match x with
    | inr' b => Some b
    | pair' _ b => Some b
    | _ => None
end.

Instance SetP_has_products : has_products SetP.
refine
{|
  prod' := prodsum;
  proj1' := @prodsum_proj1;
  proj2' := @prodsum_proj2
|}.
Proof.
  red. intros. exists (fun x : X =>
  match f x, g x with
      | None, None => None
      | Some a, None => Some (inl' a)
      | None, Some b => Some (inr' b)
      | Some a, Some b => Some (pair' a b)
  end).
  repeat split.
    extensionality x. simpl. destruct (f x), (g x); auto.
    extensionality x. simpl. destruct (f x), (g x); auto.
    intro u; intros. extensionality x. destruct H as [Hf Hg].
    assert (f x = (u .> prodsum_proj1) x). rewrite Hf. auto.
    assert (g x = (u .> prodsum_proj2) x). rewrite Hg. auto.
    simpl in *. destruct (f x), (g x), (u x);
      try destruct p; simpl in *; try inversion H; try inversion H0; auto.
Defined.

Instance SetP_has_coproducts : has_coproducts SetP.
refine
{|
  coprod := sum;
  coproj1 := fun (A B : Set) (a : A) => Some (inl a);
  coproj2 := fun (A B : Set) (b : B) => Some (inr b);
|}.
Proof.
  red. intros. exists (fun x : A + B =>
  match x with
      | inl a => f a
      | inr b => g b
  end).
  red. repeat split. intros. destruct H as [Hf Hg].
    extensionality x. simpl. destruct x. rewrite Hf. auto.
    rewrite Hg. auto.
Defined.