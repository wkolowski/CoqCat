From Cat Require Import Cat.
From Cat.Universal Require Import Initial Terminal.
From Cat.Instances Require Import Setoids FunCat.

Set Implicit Arguments.

Class Cocone {J C : Cat} (F : Functor J C) : Type :=
{
  coapex : Ob C;
  colegs : NatTrans F (ConstFunctor coapex J);
}.

Arguments coapex [J C F] _.
Arguments colegs [J C F] _.

Class CoconeHom {J C : Cat} {F : Functor J C} (C1 C2 : Cocone F) :=
{
  mor' : Hom (@coapex J C F C1) (@coapex J C F C2);
  cond' : forall X : Ob J, component (colegs C1) X .> mor' == component (colegs C2) X
}.

Arguments mor' [J C F C1 C2] _.
Arguments cond' [J C F C1 C2] _ _.

#[refine]
#[export]
Instance CoconeHomSetoid
  {J C : Cat} {F : Functor J C} (C1 C2 : Cocone F) : Setoid (CoconeHom C1 C2) :=
{
  equiv := fun f g : CoconeHom C1 C2 => mor' f == mor' g
}.
Proof. solve_equiv. Defined.

#[refine]
#[export]
Instance CoconeComp
  {J C : Cat} {F : Functor J C} (C1 C2 C3 : Cocone F)
  (f : CoconeHom C1 C2) (g : CoconeHom C2 C3) : CoconeHom C1 C3 :=
{
  mor' := mor' f .> mor' g
}.
Proof.
  intros. rewrite <- comp_assoc. rewrite cond'.
  destruct C2. destruct g. cbn in *. apply cond'0.
Defined.

#[refine]
#[export]
Instance CoconeId {J C : Cat} {F : Functor J C} (C1 : Cocone F) : CoconeHom C1 C1 :=
{
  mor' := id (coapex C1)
}.
Proof. cat. Defined.

#[refine]
#[export]
Instance CoconeCat {J C : Cat} (F : Functor J C) : Cat :=
{
  Ob := Cocone F;
  Hom := CoconeHom;
  HomSetoid := CoconeHomSetoid;
  comp := CoconeComp;
  id := CoconeId
}.
Proof. proper. all: cat. Defined.

Definition isColimit' {J C : Cat} {F : Functor J C} (K : Cocone F) : Prop :=
  forall K' : Cocone F, exists!! _ : CoconeHom K K', True.

Definition isColimit
  {J C : Cat} {F : Functor J C}
  (colimit : Cocone F)
  (colimitMor : forall K : Cocone F, CoconeHom colimit K)
  : Prop := @isInitial (CoconeCat F) colimit colimitMor.

Definition allShapedColimits
  {J C : Cat}
  (colimit : forall (F : Functor J C), Cocone F)
  (colimitMor : forall {F : Functor J C} (K : Cocone F), CoconeHom (colimit F) K)
  : Prop :=
    forall F : Functor J C, @isColimit J C F (colimit F) (@colimitMor F).

Definition allColimits
  {C : Cat}
  (colimit : forall {J : Cat} (F : Functor J C), Cocone F)
  (colimitMor : forall {J : Cat} {F : Functor J C} (K : Cocone F), CoconeHom (colimit F) K)
  : Prop :=
    forall (J : Cat) (F : Functor J C),
      @allShapedColimits J C (@colimit J) (@colimitMor J).

Class HasColimits (C : Cat) : Type :=
{
  colimit  : forall {J : Cat} (F : Functor J C), Cocone F;
  colimitMor : forall {J : Cat} (F : Functor J C) (K : Cocone F), CoconeHom (colimit F) K;
  (* Proper? *)
  ok : allColimits (@colimit) (@colimitMor);
}.

Arguments colimit  [C _ J] _.
Arguments colimitMor [C _ J F] _.

(* TODO : natural conditions for (co)limits *)

#[refine]
#[export]
Instance CoconeImage
  {J C D : Cat} {Diagram : Functor J C}
  (F : Functor C D) (K : Cocone Diagram) : Cocone (FunctorComp Diagram F) :=
{
  coapex := fob F (coapex K);
  colegs := {| component := fun X : Ob J => _ |}
}.
Proof.
  - cbn. apply (fmap F). exact (component (colegs K) X).
  - cat. rewrite <- fmap_comp. rewrite <- (natural (colegs K) f). cat.
Defined.

Definition cocontinuous {C D : Cat} {F : Functor C D} : Prop :=
  forall (J : Cat) (Diagram : Functor J C) (K : Cocone Diagram),
    isColimit' K -> isColimit' (CoconeImage F K).