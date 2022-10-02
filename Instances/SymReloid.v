From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct.
From Cat Require Export Instances.Reloid.

Set Implicit Arguments.

Class SymReloid : Type :=
{
  reloid : Reloid;
  rel_symmetric :> Symmetric rel;
}.

Coercion reloid : SymReloid >-> Reloid.

Ltac sreloidob X := try intros until X;
match type of X with
| SymReloid =>
  let a := fresh X "_rel_symmetric" in destruct X as [X a]; reloidob X
| Ob _ => progress cbn in X; sreloidob X
end.

Ltac sreloidobs := repeat
match goal with
| X : SymReloid |- _ => sreloidob X
| X : Ob _ |- _ => sreloidob X
end.

Ltac sreloidhom f := reloidhom f.

Ltac sreloidhoms := reloidhoms.

Ltac sreloid := intros; repeat
match goal with
| |- Equivalence _ => solve_equiv
| |- Proper _ _ => proper
| _ => repeat (my_simpl || sreloidobs || sreloidhoms || cat)
end.

#[refine]
#[export]
Instance SymReloidCat : Cat :=
{
  Ob := SymReloid;
  Hom := ReloidHom;
  HomSetoid := ReloidHomSetoid;
  comp := @ReloidComp;
  id := @ReloidId;
}.
Proof. all: now sreloid. Defined.

#[refine]
#[export]
Instance SymReloid_init : SymReloid :=
{
  reloid := Reloid_init;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance SymReloid_create (X : SymReloid) : ReloidHom SymReloid_init X :=
{
  func := Reloid_create X
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance HasInit_SymReloid : HasInit SymReloidCat :=
{
  init := SymReloid_init;
  create := SymReloid_create
}.
Proof. easy. Defined.

#[export]
Instance HasStrictInit_SymReloid : HasStrictInit SymReloidCat.
Proof.
  intros A f.
  exists (create A); split.
  - now intros x; destruct (f x).
  - now apply equiv_initial.
Defined.

#[refine]
#[export]
Instance SymReloid_term : SymReloid :=
{
  reloid := Reloid_term;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance SymReloid_delete (X : SymReloid) : ReloidHom X SymReloid_term :=
{
  func := Reloid_delete X
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance HasTerm_SymReloid : HasTerm SymReloidCat :=
{
  term := SymReloid_term;
  delete := SymReloid_delete;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance SymReloid_product (X Y : SymReloid) : SymReloid :=
{
  reloid := Reloid_product X Y;
}.
Proof.
  now intros [] []; cbn.
Defined.

#[refine]
#[export]
Instance SymReloid_outl (X Y : SymReloid) : ReloidHom (SymReloid_product X Y) X :=
{
  func := Reloid_outl X Y
}.
Proof.
  now intros [] []; cbn.
Defined.

#[refine]
#[export]
Instance SymReloid_outr (X Y : SymReloid) : ReloidHom (SymReloid_product X Y) Y :=
{
  func := Reloid_outr X Y
}.
Proof.
  now intros [] []; cbn.
Defined.

#[refine]
#[export]
Instance SymReloid_fpair
  (X Y A : SymReloid) (f : ReloidHom A X) (g : ReloidHom A Y)
  : ReloidHom A (SymReloid_product X Y) :=
{
  func := Reloid_fpair f g
}.
Proof.
  now split; apply pres_rel.
Defined.

#[refine]
#[export]
Instance HasProducts_SymReloid : HasProducts SymReloidCat :=
{
  product := SymReloid_product;
  outl := SymReloid_outl;
  outr := SymReloid_outr;
  fpair := SymReloid_fpair;
}.
Proof.
  now repeat split; cbn in *.
Defined.

#[refine]
#[export]
Instance SymReloid_coproduct (X Y : SymReloid) : SymReloid :=
{
  reloid := Reloid_coproduct X Y;
}.
Proof. now intros [] []; cbn. Defined.

#[refine]
#[export]
Instance SymReloid_finl (X Y : SymReloid) : ReloidHom X (SymReloid_coproduct X Y) :=
{
  func := Reloid_finl X Y;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance SymReloid_finr (X Y : SymReloid) : ReloidHom Y (SymReloid_coproduct X Y) :=
{
  func := Reloid_finr X Y;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance SymReloid_copair
  (X Y A : SymReloid) (f : ReloidHom X A) (g : ReloidHom Y A)
  : ReloidHom (SymReloid_coproduct X Y) A :=
{
  func := Reloid_copair f g
}.
Proof.
  now proper; destruct x, y; try apply pres_rel.
Defined.

#[refine]
#[export]
Instance HasCoproducts_SymReloid : HasCoproducts SymReloidCat :=
{
  coproduct := SymReloid_coproduct;
  finl := SymReloid_finl;
  finr := SymReloid_finr;
  copair := SymReloid_copair;
}.
Proof.
  split; cbn.
  - easy.
  - easy.
  - now intros P' h1 h2 HA HB [a | b].
Defined.