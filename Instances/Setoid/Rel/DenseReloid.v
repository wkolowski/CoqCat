From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct IndexedProduct IndexedCoproduct.
From Cat Require Export Instances.Setoid.Rel.Reloid.

Set Implicit Arguments.

Class Dense {A : Type} (R : A -> A -> Prop) : Prop :=
{
  dense : forall x y : A, R x y -> exists z : A, R x z /\ R z y
}.

Class DenseReloid : Type :=
{
  reloid : Reloid;
  is_dense :> Dense rel;
}.

Coercion reloid : DenseReloid >-> Reloid.

Ltac dreloidob X := try intros until X;
match type of X with
| DenseReloid =>
  let a := fresh X "_rel_is_dense" in destruct X as [X [a]]; reloidob X
| Ob _ => progress cbn in X; dreloidob X
end.

Ltac dreloidobs := repeat
match goal with
| X : DenseReloid |- _ => dreloidob X
| X : Ob _ |- _ => dreloidob X
end.

Ltac dreloidhom f := reloidhom f.

Ltac dreloidhoms := reloidhoms.

Ltac dreloid := intros; repeat
match goal with
| |- Equivalence _ => solve_equiv
| |- Proper _ _ => proper
| _ => repeat (my_simpl || dreloidobs || dreloidhoms || cat)
end.

#[refine]
#[export]
Instance DenseReloidCat : Cat :=
{
  Ob := DenseReloid;
  Hom := ReloidHom;
  HomSetoid := ReloidHomSetoid;
  comp := @ReloidComp;
  id := @ReloidId;
}.
Proof. all: dreloid. Defined.

#[refine]
#[export]
Instance DenseReloid_init : DenseReloid :=
{
  reloid := Reloid_init
}.
Proof.
  split. cbn. inversion 1.
Defined.

#[refine]
#[export]
Instance DenseReloid_create (X : DenseReloid) : ReloidHom DenseReloid_init X :=
{
  func := Reloid_create X
}.
Proof. proper. destruct x. Defined.

#[refine]
#[export]
Instance HasInit_DenseReloid : HasInit DenseReloidCat :=
{
  init := DenseReloid_init;
  create := DenseReloid_create
}.
Proof. dreloid. Defined.

#[refine]
#[export]
Instance DenseReloid_term : DenseReloid :=
{
  reloid := Reloid_term
}.
Proof.
  now cbn.
Defined.

#[refine]
#[export]
Instance DenseReloid_delete (X : DenseReloid) : ReloidHom X DenseReloid_term :=
{
  func := Reloid_delete X
}.
Proof. proper. Defined.

#[refine]
#[export]
Instance HasTerm_DenseReloid : HasTerm DenseReloidCat :=
{
  term := DenseReloid_term;
  delete := DenseReloid_delete;
}.
Proof. dreloid. Defined.

#[refine]
#[export]
Instance DenseReloid_product (X Y : DenseReloid) : DenseReloid :=
{
  reloid := Reloid_product X Y
}.
Proof.
  split. destruct x, y, 1. dreloid.
  destruct
    (X_rel_is_dense c c1) as [z1 [Hz1 Hz1']],
    (Y_rel_is_dense c0 c2) as [z2 [Hz2 Hz2']]; auto.
  now exists (z1, z2).
Defined.

#[refine]
#[export]
Instance DenseReloid_outl (X Y : DenseReloid) : ReloidHom (DenseReloid_product X Y) X :=
{
  func := Reloid_outl X Y
}.
Proof. reloid. Defined.

#[refine]
#[export]
Instance DenseReloid_outr (X Y : DenseReloid) : ReloidHom (DenseReloid_product X Y) Y :=
{
  func := Reloid_outr X Y
}.
Proof. reloid. Defined.

#[refine]
#[export]
Instance DenseReloid_fpair
  (X Y A : DenseReloid) (f : ReloidHom A X) (g : ReloidHom A Y)
  : ReloidHom A (DenseReloid_product X Y) :=
{
  func := Reloid_fpair f g
}.
Proof. reloid. Defined.

#[refine]
#[export]
Instance HasProducts_DenseReloid : HasProducts DenseReloidCat :=
{
  product := DenseReloid_product;
  outl := DenseReloid_outl;
  outr := DenseReloid_outr;
  fpair := DenseReloid_fpair;
}.
Proof.
  all: unfold isProduct; dreloid.
Defined.

#[refine]
#[export]
Instance DenseReloid_coproduct (X Y : DenseReloid) : DenseReloid :=
{
  reloid := Reloid_coproduct X Y
}.
Proof.
  split. destruct x, y; intro; cbn in H; intuition eauto;
  destruct (dense c c0) as [x [H1 H2]]; auto.
    exists (inl x). eauto.
    exists (inr x). eauto.
Defined.

#[refine]
#[export]
Instance DenseReloid_finl (X Y : DenseReloid) : ReloidHom X (DenseReloid_coproduct X Y) :=
{
  func := Reloid_finl X Y
}.
Proof. dreloid. Defined.

#[refine]
#[export]
Instance DenseReloid_finr (X Y : DenseReloid) : ReloidHom Y (DenseReloid_coproduct X Y) :=
{
  func := Reloid_finr X  Y
}.
Proof. dreloid. Defined.

#[refine]
#[export]
Instance DenseReloid_copair
  (X Y A : DenseReloid) (f : ReloidHom X A) (g : ReloidHom Y A)
  : ReloidHom (DenseReloid_coproduct X Y) A :=
{
  func := Reloid_copair f g
}.
Proof.
  proper. now destruct x, y; try apply pres_rel.
Defined.

#[refine]
#[export]
Instance HasCoproducts_DenseReloid : HasCoproducts DenseReloidCat :=
{
  coproduct := DenseReloid_coproduct;
  finl := DenseReloid_finl;
  finr := DenseReloid_finr;
  copair := DenseReloid_copair;
}.
Proof.
  proper. now destruct x1; rewrite ?H, ?H0.
  unfold isCoproduct. cat. now destruct x; rewrite ?H, ?H0.
Defined.