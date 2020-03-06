Require Import Cat.
Require Import Cat.Functor.
Require Import Cat.NatTrans.
Require Import Cat.Limits.InitTerm.

Set Implicit Arguments.

Class Cone {J C : Cat} (F : Functor J C) : Type :=
{
    apex : Ob C;
    legs : NatTrans (ConstFunctor apex J) F;
}.

Arguments apex [J C F] _.
Arguments legs [J C F] _.

Class ConeHom {J C : Cat} {F : Functor J C}
    (C1 C2 : Cone F) :=
{
    mor : Hom (apex C1) (apex C2);
    cond :
      forall X : Ob J,
        mor .> component (legs C2) X == component (legs C1) X
}.

Arguments mor [J C F C1 C2] _.
Arguments cond [J C F C1 C2] _ _.

#[refine]
Instance ConeHomSetoid {J C : Cat} {F : Functor J C}
    (C1 C2 : Cone F) : Setoid (ConeHom C1 C2) :=
{
    equiv := fun f g : ConeHom C1 C2 => mor f == mor g
}.
Proof. solve_equiv. Defined.

#[refine]
Instance ConeComp {J C : Cat} {F : Functor J C}
   (C1 C2 C3 : Cone F) (f : ConeHom C1 C2) (g : ConeHom C2 C3)
    : ConeHom C1 C3 :=
{
    mor := mor f .> mor g
}.
Proof.
  intros. rewrite !comp_assoc, !cond. reflexivity.
Defined.

#[refine]
Instance ConeId {J C : Cat} {F : Functor J C}
   (C1 : Cone F) : ConeHom C1 C1 :=
{
    mor := id (apex C1)
}.
Proof. cat. Defined.

#[refine]
Instance ConeCat {J C : Cat} (F : Functor J C) : Cat :=
{
    Ob := Cone F;
    Hom := ConeHom;
    HomSetoid := ConeHomSetoid;
    comp := ConeComp;
    id := ConeId
}.
Proof. proper. all: cat. Defined.

Definition limit {J C : Cat} {F : Functor J C}
    (K : Cone F) (del : forall K' : Cone F, ConeHom K' K)
    : Prop := @terminal (ConeCat F) K del.

Definition limit' {J C : Cat} {F : Functor J C} (K : Cone F) : Prop :=
    forall K' : Cone F, exists!! _ : ConeHom K' K, True.

Class Cocone {J C : Cat} (F : Functor J C) : Type :=
{
    coapex : Ob C;
    colegs : NatTrans F (ConstFunctor coapex J);
}.

Arguments coapex [J C F] _.
Arguments colegs [J C F] _.

Class CoconeHom {J C : Cat} {F : Functor J C}
    (C1 C2 : Cocone F) :=
{
    mor' : Hom (@coapex J C F C1) (@coapex J C F C2);
    cond' : forall X : Ob J,
        component (colegs C1) X .> mor' == component (colegs C2) X
}.

Arguments mor' [J C F C1 C2] _.
Arguments cond' [J C F C1 C2] _ _.

#[refine]
Instance CoconeHomSetoid {J C : Cat} {F : Functor J C}
    (C1 C2 : Cocone F) : Setoid (CoconeHom C1 C2) :=
{
    equiv := fun f g : CoconeHom C1 C2 => mor' f == mor' g
}.
Proof. solve_equiv. Defined.

#[refine]
Instance CoconeComp {J C : Cat} {F : Functor J C}
   (C1 C2 C3 : Cocone F) (f : CoconeHom C1 C2) (g : CoconeHom C2 C3)
    : CoconeHom C1 C3 :=
{
    mor' := mor' f .> mor' g
}.
Proof.
  intros. rewrite <- comp_assoc. rewrite cond'.
  destruct C2. destruct g. simpl in *. apply cond'0.
Defined.

#[refine]
Instance CoconeId {J C : Cat} {F : Functor J C}
   (C1 : Cocone F) : CoconeHom C1 C1 :=
{
    mor' := id (coapex C1)
}.
Proof. cat. Defined.

#[refine]
Instance CoconeCat {J C : Cat} (F : Functor J C) : Cat :=
{
    Ob := Cocone F;
    Hom := CoconeHom;
    HomSetoid := CoconeHomSetoid;
    comp := CoconeComp;
    id := CoconeId
}.
Proof. proper. all: cat. Defined.

Definition colimit {J C : Cat} {F : Functor J C}
    (K : Cocone F) (create : forall K' : Cocone F, CoconeHom K K')
    : Prop := @initial (CoconeCat F) K create.

Definition colimit' {J C : Cat} {F : Functor J C} (K : Cocone F) : Prop :=
    forall K' : Cocone F, exists!! _ : CoconeHom K K', True.

(* TODO : coherence conditions for (co)limits *)

#[refine]
Instance ConeImage {J C D : Cat} {Diagram : Functor J C}
    (F : Functor C D) (K : Cone Diagram) : Cone (FunctorComp Diagram F) :=
{
    apex := fob F (apex K);
    legs := {| component := fun X : Ob J => _ |}
}.
Proof.
  simpl. apply (fmap F). exact (component (legs K) X).
  cat. rewrite <- pres_comp. rewrite (coherence (legs K) f). cat.
Defined.

Definition continuous {C D : Cat} {F : Functor C D} : Prop :=
  forall (J : Cat) (Diagram : Functor J C) (K : Cone Diagram),
    limit' K -> limit' (ConeImage F K).

Require Import Setoids.

Instance HomSetoid' (C : Cat) (X Y : Ob C) : Setoid' :=
{
    carrier := Hom X Y;
    setoid := HomSetoid X Y
}.

Coercion wut {C D : Cat} (F : Functor C D) : Ob (FunCat C D) := F.

Theorem limit_char :
  forall (J C : Cat) (F : Functor J C)
  (K : Cone F) (del : forall K' : Cone F, ConeHom K' K),
    @limit J C F K del <-> forall c : Ob C, @isomorphic CoqSetoid
      (HomSetoid' C c (apex K)) (HomSetoid' (FunCat J C) (ConstFunctor c J) F).
Proof. (*
  split; intros.
    red. unfold limit, terminal in H. cbn.
    esplit. Unshelve. all: cycle 2.
    esplit. Unshelve. all: cycle 3.
    cbn. intro f.
    Definition wut' (J C : Cat) (F : Functor J C) (K : Cone F) (c : Ob C)
      (f : Hom c (apex K)) : NatTrans (ConstFunctor c J) F.
    Proof.
      split with (fun j => f .> component (legs K) j). cat.
          destruct K, legs0. cbn in *. rewrite coherence. cat.
    Defined.
    eapply wut'; eauto. proper. red. cbn.
    esplit. Unshelve. all: cycle 2. red. cbn.
    esplit. Unshelve. all: cycle 3.
    destruct 1. cbn in *.
    Definition wut'' (J C : Cat) (F : Functor J C) (K : Cone F) (c : Ob C)
      (f : Hom c (apex K)) : NatTrans (ConstFunctor c J) F.
    Proof.
      split with (fun j => f .> component (legs K) j). cat.
          destruct K, legs0. cbn in *. rewrite coherence. cat.
    Defined.
    pose (w := wut'' K c).
    destruct K. cbn in *.
    destruct legs0. cbn in *.
    proper. repeat red. cbn. *)
Abort.

(*Theorem limit_char :
  forall (J C : Cat) (F : Functor J C)
  (K : Cone F) (del : forall K' : Cone F, ConeHom K' K),
    @limit J C F K del <-> exists α : NatTrans (ConstFunctor c J) F,
      natural_isomorphism α.

forall c : Ob C, @isomorphic CoqSetoid
      (HomSetoid' C c (apex K)) (HomSetoid' (FunCat J C) (ConstFunctor c J) F).
Proof.
*)