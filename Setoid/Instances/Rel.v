Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Cat.
(*Require Import InitTerm.
Require Import BinProdCoprod.*)

Print Setoid.

Instance Rel : Cat :=
{|
    Ob := Set;
    Hom := fun A B : Set => A -> B -> Prop;
    Hom_Setoid := fun A B : Set =>
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
  (* Comp_assoc *) split; intros.
    (* -> *) destruct H as [b1 [[b2 [H1 H2]] H3]]. eauto.
    (* <- *) destruct H as [b1 [H3 [b2 [H1 H2]]]]. eauto.
  (* id_right *) split; intros; repeat destruct H; eauto.
  (* id_left *) split; intros; repeat destruct H; subst; eauto.
Defined.

Theorem Rel_product : forall A B : Ob Rel,
    product 
