From Cat Require Export Cat.
From Cat.Limits Require Import InitTerm ProdCoprod IndexedProdCoprod.
From Cat Require Export Instances.Setoid.Rel.Reloid.

Set Implicit Arguments.

Class TransReloid : Type :=
{
  reloid : Reloid;
  rel_transitive :> Transitive rel;
}.

Coercion reloid : TransReloid >-> Reloid.

Ltac treloidob X := try intros until X;
match type of X with
| TransReloid =>
  let a := fresh X "_rel_transitive" in destruct X as [X a]; reloidob X
| Ob _ => progress cbn in X; treloidob X
end.

Ltac treloidobs := repeat
match goal with
| X : TransReloid |- _ => treloidob X
| X : Ob _ |- _ => treloidob X
end.

Ltac treloidhom f := reloidhom f.

Ltac treloidhoms := reloidhoms.

Ltac treloid := intros; repeat
match goal with
| |- Equivalence _ => solve_equiv
| |- Proper _ _ => proper
| _ => repeat (my_simpl || treloidobs || treloidhoms || cat)
end.

#[refine]
#[export]
Instance TransReloidCat : Cat :=
{
  Ob := TransReloid;
  Hom := ReloidHom;
  HomSetoid := ReloidHomSetoid;
  comp := @ReloidComp;
  id := @ReloidId;
}.
Proof. all: treloid. Defined.

#[refine]
#[export]
Instance TransReloid_init : TransReloid :=
{
  reloid := Reloid_init;
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_create (X : TransReloid) : ReloidHom TransReloid_init X :=
{
  func := Reloid_create X
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_HasInit : HasInit TransReloidCat :=
{
  init := TransReloid_init;
  create := TransReloid_create
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_term : TransReloid :=
{
  reloid := Reloid_term;
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_delete (X : TransReloid) : ReloidHom X TransReloid_term :=
{
  func := Reloid_delete X
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_HasTerm : HasTerm TransReloidCat :=
{
  term := TransReloid_term;
  delete := TransReloid_delete;
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_prodOb (X Y : TransReloid) : TransReloid :=
{
  reloid := Reloid_prodOb X Y;
}.
Proof. split; cbn; treloid. Defined.

#[refine]
#[export]
Instance TransReloid_proj1 (X Y : TransReloid) : ReloidHom (TransReloid_prodOb X Y) X :=
{
  func := Reloid_proj1 X Y
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_proj2 (X Y : TransReloid) : ReloidHom (TransReloid_prodOb X Y) Y :=
{
  func := Reloid_proj2 X Y
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_fpair
  (X Y A : TransReloid) (f : ReloidHom A X) (g : ReloidHom A Y)
  : ReloidHom A (TransReloid_prodOb X Y) :=
{
  func := Reloid_fpair f g
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_HasProducts : HasProducts TransReloidCat :=
{
  prodOb := TransReloid_prodOb;
  proj1 := TransReloid_proj1;
  proj2 := TransReloid_proj2;
  fpair := TransReloid_fpair;
}.
Proof.
  all: unfold product_skolem; reloid.
Defined.

#[refine]
#[export]
Instance TransReloid_coprodOb (X Y : TransReloid) : TransReloid :=
{
  reloid := Reloid_coprodOb X Y;
}.
Proof. intros [] [] []; cbn; treloid. Defined.

#[refine]
#[export]
Instance TransReloid_coproj1 (X Y : TransReloid) : ReloidHom X (TransReloid_coprodOb X Y) :=
{
  func := Reloid_coproj1 X Y;
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_coproj2 (X Y : TransReloid) : ReloidHom Y (TransReloid_coprodOb X Y) :=
{
  func := Reloid_coproj2 X Y;
}.
Proof. treloid. Defined.

#[refine]
#[export]
Instance TransReloid_copair
  (X Y A : TransReloid) (f : ReloidHom X A) (g : ReloidHom Y A)
  : ReloidHom (TransReloid_coprodOb X Y) A :=
{
  func := Reloid_copair f g
}.
Proof.
  proper. destruct x, y; try apply pres_rel; intuition eauto.
Defined.

#[refine]
#[export]
Instance TransReloid_HasCoproducts : HasCoproducts TransReloidCat :=
{
  coprodOb := TransReloid_coprodOb;
  coproj1 := TransReloid_coproj1;
  coproj2 := TransReloid_coproj2;
  copair := TransReloid_copair;
}.
Proof.
  proper. destruct x1; rewrite ?H, ?H0; reflexivity.
  unfold coproduct_skolem. cat. destruct x; rewrite ?H, ?H0; reflexivity.
Defined.