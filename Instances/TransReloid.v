From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct.
From Cat Require Export Instances.Reloid.

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
Proof. all: now treloid. Defined.

#[refine]
#[export]
Instance TransReloid_init : TransReloid :=
{
  reloid := Reloid_init;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance TransReloid_create (X : TransReloid) : ReloidHom TransReloid_init X :=
{
  func := Reloid_create X
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance HasInit_TransReloid : HasInit TransReloidCat :=
{
  init := TransReloid_init;
  create := TransReloid_create
}.
Proof. easy. Defined.

#[export]
Instance HasStrictInit_TransReloid : HasStrictInit TransReloidCat.
Proof.
  intros A f.
  exists (create A); split.
  - now intros x; destruct (f x).
  - now apply equiv_initial.
Defined.

#[refine]
#[export]
Instance TransReloid_term : TransReloid :=
{
  reloid := Reloid_term;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance TransReloid_delete (X : TransReloid) : ReloidHom X TransReloid_term :=
{
  func := Reloid_delete X
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance HasTerm_TransReloid : HasTerm TransReloidCat :=
{
  term := TransReloid_term;
  delete := TransReloid_delete;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance TransReloid_product (X Y : TransReloid) : TransReloid :=
{
  reloid := Reloid_product X Y;
}.
Proof.
  now intros [a1 b1] [a2 b2] [a3 b3]; cbn; treloid.
Defined.

#[refine]
#[export]
Instance TransReloid_outl (X Y : TransReloid) : ReloidHom (TransReloid_product X Y) X :=
{
  func := Reloid_outl X Y
}.
Proof. now intros [] []; cbn. Defined.

#[refine]
#[export]
Instance TransReloid_outr (X Y : TransReloid) : ReloidHom (TransReloid_product X Y) Y :=
{
  func := Reloid_outr X Y
}.
Proof. now intros [] []; cbn. Defined.

#[refine]
#[export]
Instance TransReloid_fpair
  (X Y A : TransReloid) (f : ReloidHom A X) (g : ReloidHom A Y)
  : ReloidHom A (TransReloid_product X Y) :=
{
  func := Reloid_fpair f g
}.
Proof. now split; apply pres_rel. Defined.

#[refine]
#[export]
Instance HasProducts_TransReloid : HasProducts TransReloidCat :=
{
  product := TransReloid_product;
  outl := TransReloid_outl;
  outr := TransReloid_outr;
  fpair := TransReloid_fpair;
}.
Proof.
  now repeat split; cbn in *.
Defined.

#[refine]
#[export]
Instance TransReloid_coproduct (X Y : TransReloid) : TransReloid :=
{
  reloid := Reloid_coproduct X Y;
}.
Proof. now intros [] [] []; cbn; treloid. Defined.

#[refine]
#[export]
Instance TransReloid_finl (X Y : TransReloid) : ReloidHom X (TransReloid_coproduct X Y) :=
{
  func := Reloid_finl X Y;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance TransReloid_finr (X Y : TransReloid) : ReloidHom Y (TransReloid_coproduct X Y) :=
{
  func := Reloid_finr X Y;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance TransReloid_copair
  (X Y A : TransReloid) (f : ReloidHom X A) (g : ReloidHom Y A)
  : ReloidHom (TransReloid_coproduct X Y) A :=
{
  func := Reloid_copair f g
}.
Proof.
  now proper; destruct x, y; try apply pres_rel.
Defined.

#[refine]
#[export]
Instance HasCoproducts_TransReloid : HasCoproducts TransReloidCat :=
{
  coproduct := TransReloid_coproduct;
  finl := TransReloid_finl;
  finr := TransReloid_finr;
  copair := TransReloid_copair;
}.
Proof.
  split; cbn.
  - easy.
  - easy.
  - now intros P' h1 h2 HA HB [a | b].
Defined.