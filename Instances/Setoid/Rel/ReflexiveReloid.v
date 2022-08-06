From Cat Require Export Cat.
From Cat.Limits Require Import InitTerm ProdCoprod IndexedProdCoprod.
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
Instance ReflexiveReloid_prodOb (X Y : ReflexiveReloid) : ReflexiveReloid :=
{
  reloid := Reloid_prodOb X Y;
}.
Proof.
  split; cbn; reflexivity.
Defined.

#[refine]
#[export]
Instance ReflexiveReloid_proj1
  (X Y : ReflexiveReloid) : ReloidHom (ReflexiveReloid_prodOb X Y) X :=
{
  func := Reloid_proj1 X Y
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_proj2
  (X Y : ReflexiveReloid) : ReloidHom (ReflexiveReloid_prodOb X Y) Y :=
{
  func := Reloid_proj2 X Y
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_fpair
  (X Y A : ReflexiveReloid) (f : ReloidHom A X) (g : ReloidHom A Y)
  : ReloidHom A (ReflexiveReloid_prodOb X Y) :=
{
  func := Reloid_fpair f g
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance HasProducts_ReflexiveReloid : HasProducts ReflexiveReloidCat :=
{
  prodOb := ReflexiveReloid_prodOb;
  outl := ReflexiveReloid_proj1;
  outr := ReflexiveReloid_proj2;
  fpair := ReflexiveReloid_fpair;
}.
Proof.
  all: unfold product; reloid.
Defined.

#[refine]
#[export]
Instance ReflexiveReloid_coprodOb (X Y : ReflexiveReloid) : ReflexiveReloid :=
{
  reloid := Reloid_coprodOb X Y;
}.
Proof. intros []; cbn; reflexivity. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_finl
  (X Y : ReflexiveReloid) : ReloidHom X (ReflexiveReloid_coprodOb X Y) :=
{
  func := Reloid_finl X Y;
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_finr
  (X Y : ReflexiveReloid) : ReloidHom Y (ReflexiveReloid_coprodOb X Y) :=
{
  func := Reloid_finr X Y;
}.
Proof. rreloid. Defined.

#[refine]
#[export]
Instance ReflexiveReloid_copair
  (X Y A : ReflexiveReloid) (f : ReloidHom X A) (g : ReloidHom Y A)
  : ReloidHom (ReflexiveReloid_coprodOb X Y) A :=
{
  func := Reloid_copair f g
}.
Proof.
  proper. destruct x, y; try apply pres_rel; intuition eauto.
Defined.

#[refine]
#[export]
Instance HasCoproducts_ReflexiveReloid : HasCoproducts ReflexiveReloidCat :=
{
  coprodOb := ReflexiveReloid_coprodOb;
  finl := ReflexiveReloid_finl;
  finr := ReflexiveReloid_finr;
  copair := ReflexiveReloid_copair;
}.
Proof.
  proper. destruct x1; rewrite ?H, ?H0; reflexivity.
  unfold coproduct. cat. destruct x; rewrite ?H, ?H0; reflexivity.
Defined.