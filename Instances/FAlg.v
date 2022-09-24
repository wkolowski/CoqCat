From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct.

Definition FAlg {C : Cat} (F : Functor C C) : Type :=
  {X : Ob C & @Hom C (fob F X) X}.

Ltac falg_simpl := repeat red; cbn in *; intros.

Ltac falgob X := try intros until X;
match type of X with
| FAlg _ => let α := fresh "α_" X in destruct X as [X α]
| Ob _ => progress cbn in X; falgob X
end.

Ltac falgobs_template tac := repeat
match goal with
| X : FAlg _ |- _ => tac X
| X : Ob _ |- _ => tac X
end.

Ltac falgobs := falgobs_template falgob; cbn in *.

Definition FAlgHom {C : Cat} {F : Functor C C} (X Y : FAlg F) : Type :=
  {f : Hom (projT1 X) (projT1 Y) | projT2 X .> f == fmap F f .> projT2 Y}.

Ltac falghom f := try intros until f;
match type of f with
| FAlgHom _ _ => let a := fresh f "_cond" in destruct f as [f a]
| Hom _ _ => progress cbn in f; falghom f
end; falg_simpl.

Ltac falghoms_template tac := intros; repeat
match goal with
| f : FAlgHom _ _ |- _ => tac f
| f : Hom _ _ |- _ => tac f
end.

Ltac falghoms := falghoms_template falghom.

Ltac falg := repeat (falg_simpl || falgobs || falghoms || cat); unfold FAlgHom; cbn.

#[refine]
#[export]
Instance FAlgHomSetoid {C : Cat} {F : Functor C C} (X Y : FAlg F) : Setoid (FAlgHom X Y) :=
{
  equiv := fun f g : FAlgHom X Y =>
    @equiv _ (@HomSetoid C (projT1 X) (projT1 Y)) (proj1_sig f) (proj1_sig g)
}.
Proof. now apply Setoid_kernel_equiv. Defined.

Definition FAlgComp
  {C : Cat} {F : Functor C C} {X Y Z : FAlg F} (f : FAlgHom X Y) (g : FAlgHom Y Z) : FAlgHom X Z.
Proof.
  falg.
  exists (f .> g).
  now rewrite <- comp_assoc, f_cond, comp_assoc, g_cond, fmap_comp, comp_assoc.
Defined.

Definition FAlgId {C : Cat} {F : Functor C C} {X : FAlg F} : FAlgHom X X.
Proof.
  exists (@id _ (projT1 X)).
  now rewrite fmap_id, comp_id_l, comp_id_r.
Defined.

#[refine]
#[export]
Instance CatFAlg {C : Cat} (F : Functor C C) : Cat :=
{
  Ob := @FAlg C F;
  Hom := @FAlgHom C F;
  HomSetoid := @FAlgHomSetoid C F;
  comp := @FAlgComp C F;
  id := @FAlgId C F
}.
Proof.
  - intros [X x] [Y y] [Z z] [f1 Hf1] [f2 Hf2] Hf [g1 Hg1] [g2 Hg2] Hg; cbn in *.
    now rewrite Hf, Hg.
  - intros [X x] [Y y] [Z z] [W w] [f Hf] [g Hg] [h Hh]; cbn in *.
    now rewrite comp_assoc.
  - intros [X x] [Y y] [f Hf]; cbn in *.
    now rewrite comp_id_l.
  - intros [X x] [Y y] [f Hf]; cbn in *.
    now rewrite comp_id_r.
Defined.