Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Instance Rel : Cat :=
{|
    Ob := Set;
    Hom := fun A B : Set => A -> B -> Prop;
    HomSetoid := fun A B : Set =>
        {| equiv := fun R S : (A -> B -> Prop) =>
            forall (a : A) (b : B), R a b <-> S a b |};
    comp := fun (A B C : Set) (R : A -> B -> Prop) (S : B -> C -> Prop) =>
        fun (a : A) (c : C) => exists b : B, R a b /\ S b c;
    id := fun (A : Set) => fun (a1 a2 : A) => a1 = a2
|}.
Proof.
  (* Equivalence *) split.
    (* Reflexivity *) red. tauto.
    (* Symmetry *) red. intuition; [rewrite H | rewrite <- H]; auto.
    (* Transitivity *) red. intuition.
      rewrite <- H0, <- H. assumption.
      rewrite H, H0. assumption.
  (* Proper *) simpl; split; intros.
    (* -> *) destruct H1 as [b' [Hx Hx0]]. rewrite H in Hx.
      rewrite H0 in Hx0. eauto.
    (* <- *) destruct H1 as [b' [Hy Hy0]]. rewrite <- H in Hy.
      rewrite <- H0 in Hy0. eauto.
  (* Category laws *) all: cat.
Defined.

Instance Rel_has_init : has_init Rel :=
{
    init := Empty_set;
    create := fun (X : Set) (e : Empty_set) (x : X) => match e with end
}.
Proof. split; intros; destruct a. Defined.

Instance Rel_has_term : has_term Rel :=
{
    term := Empty_set;
    delete := fun (X : Set) (x : X) (e : Empty_set) => match e with end
}.
Proof. split; intros. destruct b. destruct b. Defined.

Instance Rel_has_zero : has_zero Rel :=
{
    zero := Empty_set
}.
Proof.
  repeat (red || split); simpl; intros.
    exists (fun (e : Empty_set) _ => match e with end).
      repeat (red || split || intros). all: try destruct a.
    exists (fun _ (e : Empty_set) => match e with end).
      repeat (red || split || intros). all: try destruct b.
Restart.
  repeat (red || split); simpl; intros.
    exists (fun (e : Empty_set) _ => match e with end).
      cat; destruct a.
    exists (fun _ (e : Empty_set) => match e with end).
      cat; destruct b.
Defined.

Inductive relprod (A B : Set) : Type :=
    | inl' : A -> relprod A B
    | inr' : B -> relprod A B
    | pair' : A -> B -> relprod A B.

Arguments inl' [A] [B] _.
Arguments inr' [A] [B] _.
Arguments pair' [A] [B] _ _.

Theorem Rel_product : forall A B : Ob Rel,
    product Rel (relprod A B)
      (fun (p : relprod A B) (a : A) =>
        p = inl' a \/ exists b : B, p = pair' a b)
      (fun (p : relprod A B) (b : B) =>
        p = inr' b \/ exists a : A, p = pair' a b).
Proof.
  unfold product; simpl; intros A B X R S.
  exists (fun (x : X) (p : relprod A B) => match p with
    | inl' a => R x a
    | inr' b => S x b
    | pair' a b => R x a /\ S x b
  end).
  repeat red. do 2 split. intros x a. split; intros.
    exists (inl' a). split; auto.
    destruct H. destruct x0. destruct H, H0. inversion H0; subst. auto.
      destruct H0. inversion H0.
    destruct H as [_ [F | [b0 F]]]; inversion F.
    destruct H as [[HR HS] [HF | [b0 H]]]. inversion HF.
      inversion H; subst. auto.
  intros x b. split; intros.
    exists (inr' b). split; auto.
    destruct H, x0. destruct H, H0; inversion H0. inversion H1.
    destruct H, H0. inversion H0; subst; auto. destruct H0. inversion H0.
    repeat destruct H; destruct H0. inversion H0.
      destruct H0. inversion H0; subst; auto.
  destruct H, b; intros.
    rewrite H in H1. destruct H1 as [b [H2 [H3 | H4]]].
      subst. auto.
      destruct H4. destruct b; inversion H1. subst.

Theorem Rel_product : forall A B : Ob Rel,
    product Rel (A + B) (fun (p : A + B) (a : A) => p = inl a)
      (fun (p : A + B) (b : B) => p = inr b).
Proof.
  unfold product; simpl; intros.
  exists 

Theorem Rel_product : forall A B : Ob Rel,
    product Rel (A * B) (fun (p : A * B) (a : A) => fst p = a)
      (fun (p : A * B) (b : B) => snd p = b).
Proof.
  unfold product; simpl; intros.
  exists (fun (x : X) (p : A * B) => f x (fst p) /\ g x (snd p)).
  repeat red; repeat split; intros.
  Focus 2. repeat destruct H. rewrite H0 in H. auto.
  Focus 3. repeat destruct H. rewrite H0 in H1. auto.
  Focus 3. destruct H, H0. destruct (H a (fst b)), (H1 a (snd b)).
    destruct (H3 H0). destruct H7. destruct (H5 H2). destruct H9.
    destruct b. simpl in *. destruct x, x0. simpl in *.  
