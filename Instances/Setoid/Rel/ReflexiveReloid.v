From Cat Require Export Cat.
From Cat.Limits Require Import Initial Terminal Product Coproduct.
From Cat.Limits.Indexed Require Import Product Coproduct.
From Cat Require Export Instances.Setoid.Rel.Reloid.

Set Implicit Arguments.

Class ReflexiveReloid : Type :=
{
  reloid : Reloid;
  rel_reflexive :> Reflexive rel;
}.

Coercion reloid : ReflexiveReloid >-> Reloid.

Ltac rreloidob X := try intros until X;
match type of X with
| ReflexiveReloid =>
  let a := fresh X "_rel_reflexive" in destruct X as [X a]; reloidob X
| Ob _ => progress cbn in X; rreloidob X
end.

Ltac rreloidobs := repeat
match goal with
| X : ReflexiveReloid |- _ => rreloidob X
| X : Ob _ |- _ => rreloidob X
end.

Ltac rreloidhom f := reloidhom f.

Ltac rreloidhoms := reloidhoms.

Ltac rreloid := intros; repeat
match goal with
| |- Equivalence _ => solve_equiv
| |- Proper _ _ => proper
| _ => repeat (my_simpl || rreloidobs || rreloidhoms || cat)
end.

#[refine]
#[export]
Instance ReflexiveReloidCat : Cat :=
{
  Ob := ReflexiveReloid;
  Hom := ReloidHom;
  HomSetoid := ReloidHomSetoid;
  comp := @ReloidComp;
  id := @ReloidId;
}.
Proof. all: rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_init : ReflexiveReloid :=
{
  reloid := Reloid_init;
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_create (X : ReflexiveReloid) : ReloidHom ReflexiveReloid_init X :=
{
  func := Reloid_create X
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance HasInit_ReflexiveReloid : HasInit ReflexiveReloidCat :=
{
  init := ReflexiveReloid_init;
  create := ReflexiveReloid_create
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_term : ReflexiveReloid :=
{
  reloid := Reloid_term;
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_delete (X : ReflexiveReloid) : ReloidHom X ReflexiveReloid_term :=
{
  func := Reloid_delete X
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance HasTerm_ReflexiveReloid : HasTerm ReflexiveReloidCat :=
{
  term := ReflexiveReloid_term;
  delete := ReflexiveReloid_delete;
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_product (X Y : ReflexiveReloid) : ReflexiveReloid :=
{
  reloid := Reloid_product X Y;
}.
Proof.
  easy.
Defined.

#[refine]
#[export]
Instance ReflexiveReloid_outl
  (X Y : ReflexiveReloid) : ReloidHom (ReflexiveReloid_product X Y) X :=
{
  func := Reloid_outl X Y
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_outr
  (X Y : ReflexiveReloid) : ReloidHom (ReflexiveReloid_product X Y) Y :=
{
  func := Reloid_outr X Y
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_fpair
  (X Y A : ReflexiveReloid) (f : ReloidHom A X) (g : ReloidHom A Y)
  : ReloidHom A (ReflexiveReloid_product X Y) :=
{
  func := Reloid_fpair f g
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance HasProducts_ReflexiveReloid : HasProducts ReflexiveReloidCat :=
{
  product := ReflexiveReloid_product;
  outl := ReflexiveReloid_outl;
  outr := ReflexiveReloid_outr;
  fpair := ReflexiveReloid_fpair;
}.
Proof.
  all: unfold isProduct; reloid.
Defined.

#[refine]
#[export]
Instance ReflexiveReloid_coproduct (X Y : ReflexiveReloid) : ReflexiveReloid :=
{
  reloid := Reloid_coproduct X Y;
}.
Proof. now intros []; cbn. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_finl
  (X Y : ReflexiveReloid) : ReloidHom X (ReflexiveReloid_coproduct X Y) :=
{
  func := Reloid_finl X Y;
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_finr
  (X Y : ReflexiveReloid) : ReloidHom Y (ReflexiveReloid_coproduct X Y) :=
{
  func := Reloid_finr X Y;
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_copair
  (X Y A : ReflexiveReloid) (f : ReloidHom X A) (g : ReloidHom Y A)
  : ReloidHom (ReflexiveReloid_coproduct X Y) A :=
{
  func := Reloid_copair f g
}.
Proof.
  proper. now destruct x, y; try apply pres_rel.
Defined.

#[refine]
#[export]
Instance HasCoproducts_ReflexiveReloid : HasCoproducts ReflexiveReloidCat :=
{
  coproduct := ReflexiveReloid_coproduct;
  finl := ReflexiveReloid_finl;
  finr := ReflexiveReloid_finr;
  copair := ReflexiveReloid_copair;
}.
Proof.
  proper. now destruct x1; rewrite ?H, ?H0.
  unfold isCoproduct. cat. now destruct x; rewrite ?H, ?H0.
Defined.