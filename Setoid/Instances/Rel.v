Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Print Setoid.

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
  (* Category axioms *) all: cat.
  (*(* Comp_assoc *) split; intros.
    (* -> *) destruct H as [b1 [[b2 [H1 H2]] H3]]. eauto.
    (* <- *) destruct H as [b1 [H3 [b2 [H1 H2]]]]. eauto.
  (* id_right *) split; intros; repeat destruct H; eauto.
  (* id_left *) split; intros; repeat destruct H; subst; eauto.*)
Defined.

Instance Rel_has_init' : has_init' Rel :=
{
    init' := Empty_set;
    create := fun (X : Set) (e : Empty_set) (x : X) => match e with end
}.
Proof. split; intros; destruct a. Defined.

Instance Rel_has_term' : has_term' Rel :=
{
    term' := Empty_set;
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
Defined.

Theorem Rel_product : forall A B : Ob Rel,
    product 
