From Cat Require Import Cat.
From Cat.Limits Require Import InitTerm.
From Cat.Instances Require Import Setoids FunCat.

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
Proof. solve_equiv. Defined.

#[refine]
#[export]
Instance ConeComp
  {J C : Cat} {F : Functor J C} (C1 C2 C3 : Cone F)
  (f : ConeHom C1 C2) (g : ConeHom C2 C3) : ConeHom C1 C3 :=
{
  mor := mor f .> mor g
}.
Proof.
  intros. rewrite !comp_assoc, !cond. reflexivity.
Defined.

#[refine]
#[export]
Instance ConeId {J C : Cat} {F : Functor J C} (C1 : Cone F) : ConeHom C1 C1 :=
{
  mor := id (apex C1)
}.
Proof. cat. Defined.

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
Proof. proper. all: cat. Defined.

Definition particular_limit
  {J C : Cat} {F : Functor J C}
  (limitOb : Cone F)
  (limitMor : forall K : Cone F, ConeHom K limitOb)
  : Prop := @terminal (ConeCat F) limitOb limitMor.

Definition shaped_limit
  {J C : Cat}
  (limitOb : forall F : Functor J C, Cone F)
  (limitMor : forall {F : Functor J C} (K : Cone F), ConeHom K (limitOb F))
  : Prop :=
    forall F : Functor J C, @particular_limit J C F (limitOb F) (@limitMor F).

Definition particular_limit' {J C : Cat} {F : Functor J C} (K : Cone F) : Prop :=
  forall K' : Cone F, exists!! _ : ConeHom K' K, True.

Definition limit
  {C : Cat}
  (limitOb  : forall {J : Cat} (F : Functor J C), Cone F)
  (limitMor : forall {J : Cat} (F : Functor J C) (K : Cone F), ConeHom K (limitOb F))
  : Prop :=
    forall (J : Cat) (F : Functor J C),
      @shaped_limit J C (@limitOb J) (@limitMor J).

Class HasLimits (C : Cat) : Type :=
{
  limitOb  : forall {J : Cat} (F : Functor J C), Cone F;
  limitMor : forall {J : Cat} (F : Functor J C) (K : Cone F), ConeHom K (limitOb F);
  (* Proper? *)
  isLimit : limit (@limitOb) (@limitMor);
}.

Arguments limitOb  [C _ J] _.
Arguments limitMor [C _ J F] _.

(* TODO : coherence conditions for (co)limits *)

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
  simpl. apply (fmap F). exact (component (legs K) X).
  cat. rewrite <- pres_comp. rewrite (coherence (legs K) f). cat.
Defined.

Definition continuous {C D : Cat} {F : Functor C D} : Prop :=
  forall (J : Cat) (Diagram : Functor J C) (K : Cone Diagram),
    particular_limit' K -> particular_limit' (ConeImage F K).

#[export]
Instance HomSetoid' (C : Cat) (X Y : Ob C) : Setoid' :=
{
  carrier := Hom X Y;
  setoid := HomSetoid X Y
}.

Coercion wut {C D : Cat} (F : Functor C D) : Ob (FunCat C D) := F.

Lemma limit_char
  (J C : Cat) (F : Functor J C)
  (K : Cone F) (del : forall K' : Cone F, ConeHom K' K) :
    @particular_limit J C F K del
      <->
    forall c : Ob C,
      @isomorphic CoqSetoid (HomSetoid' C c (apex K)) (HomSetoid' (FunCat J C) (ConstFunctor c J) F).
Proof.
Abort.