Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.
Require Import Exponential.

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
  (* Equivalence *) solve_equiv; try (rewrite H; try rewrite H0; auto; fail);
    try (try rewrite <- H0; rewrite <- H; auto; fail).
  (* Proper *) proper; split.
    (* -> *) destruct 1 as [b' [Hx Hx0]]. rewrite H in Hx.
      rewrite H0 in Hx0. eauto.
    (* <- *) destruct 1 as [b' [Hy Hy0]]. rewrite <- H in Hy.
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
    zero_is_initial := Rel_has_init;
    zero_is_terminal := Rel_has_term
}.
Proof. cat. Defined.

Ltac solve :=
match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | _ => try subst; eauto
end.

Definition Rel_prodOb (X Y : Set) : Set := sum X Y.

Definition Rel_proj1 {X Y : Set} (p : X + Y) (x : X)
    : Prop := p = inl x.
Definition Rel_proj2 {X Y : Set} (p : X + Y) (y : Y)
    : Prop := p = inr y.

Definition Rel_fpair {X Y A : Set} (f : A -> X -> Prop) (g : A -> Y -> Prop)
    (a : A) (p : X + Y) : Prop :=
match p with
    | inl x => f a x
    | inr y => g a y
end.

Hint Unfold Rel_prodOb Rel_proj1 Rel_proj2 Rel_fpair.

Ltac solve_Rel_core :=
match goal with
    | |- exists _, _ => eexists
    | |- _ /\ _ => split; eauto
    | x : _ + _ |- _ => destruct x
    | H : _ = _ |- _ => inversion H; subst
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : forall _ : ?T, _, x : ?T |- _ => specialize (H x)
    | H : _ <-> _ |- _ => destruct H
end.

Instance Rel_has_products : has_products Rel :=
{
    prodOb := Rel_prodOb;
    proj1 := @Rel_proj1;
    proj2 := @Rel_proj2;
    fpair := @Rel_fpair;
}.
Proof.
  proper. destruct b; split; intro; try apply H; try apply H0; assumption.
  red; cat. all: repeat (simpl in *; intros;
    unfold Rel_prodOb, Rel_proj1, Rel_proj2, Rel_fpair in *;
    solve_Rel_core; eauto).
Defined.

Definition Rel_coproj1 {X Y : Set} (x : X) (p : X + Y)
    : Prop := p = inl x.
Definition Rel_coproj2 {X Y : Set} (y : Y) (p : X + Y)
    : Prop := p = inr y.

Definition Rel_copair {X Y A : Set} (R : X -> A -> Prop) (S : Y -> A -> Prop)
    (p : X + Y) (a : A) : Prop :=
match p with
    | inl x => R x a
    | inr y => S y a
end.

Ltac solve_Rel_coprod := repeat (simpl in *; intros;
    unfold Rel_prodOb, Rel_proj1, Rel_proj2, Rel_fpair in *;
    solve_Rel_core; eauto).

Instance Rel_has_coproducts : has_coproducts Rel :=
{
    coprodOb := Rel_prodOb;
    coproj1 := @Rel_coproj1;
    coproj2 := @Rel_coproj2;
    copair := @Rel_copair;
}.
Proof.
  proper. destruct a; split; intro; try apply H; try apply H0; assumption.
  red; cat. all: repeat (simpl in *; intros;
    unfold Rel_prodOb, Rel_coproj1, Rel_coproj2, Rel_copair in *;
    solve_Rel_core; eauto).
Defined.

Instance Rel_has_biproducts : has_biproducts Rel :=
{
    products := Rel_has_products;
    coproducts := Rel_has_coproducts;
}.
Proof. simpl. trivial. Defined.

Instance Rel_has_all_products : has_all_products Rel :=
{
    bigProdOb := fun (J : Set) (A : J -> Ob Rel) => {j : J & A j};
    bigProj := fun (J : Set) (A : J -> Ob Rel) (j : J) =>
        fun (p : {j : J & A j}) (x : A j) => projT1 p = j /\ JMeq (projT2 p) x;
    bigDiag := fun (J : Set) (A : J -> Ob Rel) (X : Ob Rel)
      (f : forall j : J, Hom X (A j)) (x : X) (p : {j : J & A j}) =>
        f (projT1 p) x (projT2 p)
}.
Proof.
  (* bigDiag is proper *) cat.
  (* Product law *) red; cat; simpl in *.
    exists (existT A j b); simpl. auto.
    destruct (H x a a0), (H1 H0), x0; simpl in *. cat.
    destruct (H x a a0); simpl in *. cat.
Defined.

Instance Rel_has_all_coproducts : has_all_coproducts Rel :=
{
    bigCoprodOb := fun (J : Set) (A : J -> Ob Rel) => {j : J & A j};
    bigCoproj := fun (J : Set) (A : J -> Ob Rel) (j : J) =>
        fun (x : A j) (p : {j : J & A j}) => projT1 p = j /\ JMeq (projT2 p) x;
    bigCodiag := fun (J : Set) (A : J -> Ob Rel) (X : Ob Rel)
      (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) (x : X) =>
        f (projT1 p) (projT2 p) x
}.
Proof.
  (* bigCodiag is proper *) cat.
  (* Coproduct law *) red; cat; simpl in *.
    exists (existT A j a); simpl. auto.
    destruct (H x a b), (H1 H0), x0. cat.
    destruct (H x a b). apply H2. eexists. cat.
Defined.

Instance Rel_has_all_biproducts : has_all_biproducts Rel :=
{
    bigProduct := Rel_has_all_products;
    bigCoproduct := Rel_has_all_coproducts
}.
Proof. cat. Defined.

(* Rel doesn't have exponentials *)
(*Instance Rel_has_exponentials : has_exponentials Rel :=
{
    expOb := fun X Y : Set => X -> Y -> Prop
}.*)