Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Open Scope type_scope.

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
Proof. cat. Defined.

Instance Rel_has_term : has_term Rel :=
{
    term := Empty_set;
    delete := fun (X : Set) (x : X) (e : Empty_set) => match e with end
}.
Proof. cat. Defined.

Instance Rel_has_zero : has_zero Rel :=
{
    zero := Empty_set
}.
Proof.
  unfold zero_object, initial, terminal; cat.
    exists (fun (e : Empty_set) _ => match e with end). cat.
    exists (fun _ (e : Empty_set) => match e with end). cat.
Defined.

Instance Rel_has_zero' : has_zero' Rel :=
{
    zero_is_initial := Rel_has_init;
    zero_is_terminal := Rel_has_term
}.
Proof. cat. Defined.

Eval cbn in zero' Rel.

Ltac solve :=
match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | _ => try subst; eauto
end.

Theorem Rel_product : forall A B : Ob Rel,
    product Rel (A + B) (fun (p : A + B) (a : A) => p = inl a)
      (fun (p : A + B) (b : B) => p = inr b).
Proof.
  unfold product; simpl. intros A B X R S.
  exists (fun (x : X) (ab : A + B) => match ab with
      | inl a => R x a
      | inr b => S x b
  end).
  repeat (red || split); intros.
    exists (inl b). auto.
    destruct H, x, H; inversion H0; subst; auto.
    exists (inr b). auto.
    destruct H, x, H; inversion H0; subst; auto.
    destruct H, b. 
      destruct (H a a0), (H2 H0), H4; subst. auto.
      destruct (H1 a b), (H2 H0), H4; subst. auto.
    destruct H, b.
      destruct (H a a0). apply H3. eauto.
      destruct (H1 a b). apply H3. eauto.
Defined.

Theorem Rel_coproduct : forall A B : Ob Rel,
    coproduct Rel (A + B) (fun (a : A) (p : A + B) => p = inl a)
      (fun (b : B) (p : A + B) => p = inr b).
Proof.
  unfold coproduct; simpl. intros A B X R S.
  exists (fun (ab : A + B) (x : X) => match ab with
      | inl a => R a x
      | inr b => S b x
  end).
  repeat (red || split); intros.
    exists (inl a). auto.
    destruct H, x, H; inversion H; subst; auto.
    exists (inr a). auto.
    destruct H, x, H; inversion H; subst; auto.
    destruct H, a.
      destruct (H a b), (H2 H0), H4; subst. auto.
      destruct (H1 b0 b), (H2 H0), H4; subst. auto.
    destruct H, a.
      destruct (H a b). apply H3. eauto.
      destruct (H1 b0 b). apply H3. eauto.
Defined.

Hint Resolve Rel_product Rel_coproduct.

Theorem Rel_biproduct : forall A B : Ob Rel,
    biproduct' Rel (A + B)
      (fun (p : A + B) (a : A) => p = inl a)
      (fun (p : A + B) (b : B) => p = inr b)      
      (fun (a : A) (p : A + B) => p = inl a)
      (fun (b : B) (p : A + B) => p = inr b).
Proof. cat. Defined.

