From Cat Require Import Cat.
From Cat.Universal Require Import Initial Terminal.
From Cat.Instances Require Import SETOID.

Set Implicit Arguments.

Class Cone {J C : Cat} (F : Functor J C) : Type :=
{
  apex : Ob C;
  legs : NatTrans (ConstFunctor apex J) F;
}.

Arguments apex [J C F] _.
Arguments legs [J C F] _.

Class ConeHom {J C : Cat} {F : Functor J C} (C1 C2 : Cone F) :=
{
  mor : Hom (apex C1) (apex C2);
  cond : forall X : Ob J, mor .> component (legs C2) X == component (legs C1) X
}.

Arguments mor [J C F C1 C2] _.
Arguments cond [J C F C1 C2] _ _.

#[refine]
#[export]
Instance ConeHomSetoid
  {J C : Cat} {F : Functor J C} (C1 C2 : Cone F) : Setoid (ConeHom C1 C2) :=
{
  equiv := fun f g : ConeHom C1 C2 => mor f == mor g
}.
Proof. now solve_equiv. Defined.

#[refine]
#[export]
Instance ConeComp
  {J C : Cat} {F : Functor J C} (C1 C2 C3 : Cone F)
  (f : ConeHom C1 C2) (g : ConeHom C2 C3) : ConeHom C1 C3 :=
{
  mor := mor f .> mor g
}.
Proof.
  now intros; rewrite !comp_assoc, !cond.
Defined.

#[refine]
#[export]
Instance ConeId {J C : Cat} {F : Functor J C} (C1 : Cone F) : ConeHom C1 C1 :=
{
  mor := id (apex C1)
}.
Proof. now cat. Defined.

#[refine]
#[export]
Instance ConeCat {J C : Cat} (F : Functor J C) : Cat :=
{
  Ob := Cone F;
  Hom := ConeHom;
  HomSetoid := ConeHomSetoid;
  comp := ConeComp;
  id := ConeId
}.
Proof. all: now cat. Defined.

Definition isLimit
  {J C : Cat} {F : Functor J C}
  (limit : Cone F)
  (limitMor : forall K : Cone F, ConeHom K limit)
  : Prop := @isTerminal (ConeCat F) limit limitMor.

Definition isLimit' {J C : Cat} {F : Functor J C} (K : Cone F) : Prop :=
  forall K' : Cone F, exists!! _ : ConeHom K' K, True.

Definition allShapedLimits
  {J C : Cat}
  (limit : forall F : Functor J C, Cone F)
  (limitMor : forall {F : Functor J C} (K : Cone F), ConeHom K (limit F))
  : Prop :=
    forall F : Functor J C, @isLimit J C F (limit F) (@limitMor F).

Definition allLimits
  {C : Cat}
  (limit  : forall {J : Cat} (F : Functor J C), Cone F)
  (limitMor : forall {J : Cat} (F : Functor J C) (K : Cone F), ConeHom K (limit F))
  : Prop :=
    forall (J : Cat) (F : Functor J C),
      @allShapedLimits J C (@limit J) (@limitMor J).

Class HasLimits (C : Cat) : Type :=
{
  limit  : forall {J : Cat} (F : Functor J C), Cone F;
  limitMor : forall {J : Cat} (F : Functor J C) (K : Cone F), ConeHom K (limit F);
  (* Proper? *)
  ok : allLimits (@limit) (@limitMor);
}.

Arguments limit    [C _ J] _.
Arguments limitMor [C _ J F] _.

#[refine]
#[export]
Instance ConeImage
  {J C D : Cat} {Diagram : Functor J C}
  (F : Functor C D) (K : Cone Diagram) : Cone (FunctorComp Diagram F) :=
{
  apex := fob F (apex K);
  legs := {| component := fun X : Ob J => _ |}
}.
Proof.
  - exact (fmap F (component (legs K) X)).
  - now cbn; intros; rewrite comp_id_l, <- fmap_comp, (natural (legs K) f); cbn; rewrite comp_id_l.
Defined.

Definition isContinuous {C D : Cat} {F : Functor C D} : Prop :=
  forall (J : Cat) (Diagram : Functor J C) (K : Cone Diagram),
    isLimit' K -> isLimit' (ConeImage F K).

(*
Coercion wut {C D : Cat} (F : Functor C D) : Ob (FunCat C D) := F.

Lemma isLimit_char
  (J C : Cat) (F : Functor J C)
  (K : Cone F) (del : forall K' : Cone F, ConeHom K' K) :
    @isLimit J C F K del
      <->
    forall c : Ob C,
      @isomorphic SETOID (HomSetoid C c (apex K)) (HomSetoid (FunCat J C) (ConstFunctor c J) F).
Proof.
Abort.
*)