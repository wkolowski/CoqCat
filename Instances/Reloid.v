From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct.
From Cat Require Export Instances.SETOID.

Set Implicit Arguments.

Class Reloid : Type :=
{
  carrier : Setoid';
  rel : carrier -> carrier -> Prop;
  Proper_rel :: Proper (equiv ==> equiv ==> iff) rel
}.

Coercion carrier : Reloid >-> Setoid'.

Ltac reloidob X := try intros until X;
match type of X with
| Reloid =>
  let a := fresh X "_rel" in 
  let b := fresh X "_Proper_rel" in destruct X as [X a b]; setoidob X
| Ob _ => progress cbn in X; reloidob X
end.

Ltac reloidobs := repeat
match goal with
| X : Reloid |- _ => reloidob X
| X : Ob _ |- _ => reloidob X
end.

Class ReloidHom (X Y : Reloid) : Type :=
{
  func : SetoidHom X Y;
  pres_rel : Proper (@rel X ==> @rel Y) func
}.

Coercion func : ReloidHom >-> SetoidHom.

Ltac reloidhom f := try intros until f;
match type of f with
| ReloidHom _ _ =>
    let a := fresh f "_pres_rel" in destruct f as [f a]; setoidhom f
| Hom _ _ => progress cbn in f; reloidhom f
end.

Ltac reloidhoms := intros; repeat
match goal with
| f : ReloidHom _ _ |- _ => reloidhom f
| f : Hom _ _ |- _ => reloidhom f
| _ => idtac
end.

Ltac reloid := intros; repeat
match goal with
| |- Equivalence _ => solve_equiv
| |- Proper _ _ => proper
| _ => repeat (my_simpl || reloidobs || reloidhoms || cat)
end.

#[refine]
#[export]
Instance ReloidHomSetoid (X Y : Reloid) : Setoid (ReloidHom X Y) :=
{
  equiv := fun f g => forall x : X, f x == g x
}.
Proof. now solve_equiv. Defined.

#[refine]
#[export]
Instance ReloidComp {X Y Z : Reloid} (f : ReloidHom X Y) (g : ReloidHom Y Z) : ReloidHom X Z :=
{
  func := SetoidComp f g
}.
Proof. now reloid. Defined.

#[refine]
#[export]
Instance ReloidId (X : Reloid) : ReloidHom X X :=
{
  func := SetoidId X
}.
Proof. now reloid. Defined.

#[refine]
#[export]
Instance ReloidCat : Cat :=
{
  Ob := Reloid;
  Hom := ReloidHom;
  HomSetoid := ReloidHomSetoid;
  comp := @ReloidComp;
  id := @ReloidId;
}.
Proof. all: now reloid. Defined.

#[export]
Instance Reloid_init : Reloid :=
{
  carrier := SETOID_init;
  rel := relate_Empty;
}.

#[refine]
#[export]
Instance Reloid_create (X : Reloid) : ReloidHom Reloid_init X :=
{
  func := SETOID_create X
}.
Proof. now proper. Defined.

#[refine]
#[export]
Instance HasInit_Reloid : HasInit ReloidCat :=
{
  init := Reloid_init;
  create := Reloid_create
}.
Proof. easy. Defined.

#[export]
Instance HasStrictInit_Reloid : HasStrictInit ReloidCat.
Proof.
  intros A f.
  exists (create A); split.
  - now intros x; destruct (f x).
  - now apply equiv_initial.
Defined.

#[export]
Instance Reloid_term : Reloid :=
{
  carrier := SETOID_term;
  rel := relate_unit;
}.

#[refine]
#[export]
Instance Reloid_delete (X : Reloid) : ReloidHom X Reloid_term :=
{
  func := SETOID_delete X
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance HasTerm_Reloid : HasTerm ReloidCat :=
{
  term := Reloid_term;
  delete := Reloid_delete;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance Reloid_product (X Y : Reloid) : Reloid :=
{
  carrier := SETOID_product X Y;
  rel := relate_prod' rel rel;
}.
Proof.
  intros [f1 Hf1] [f2 Hf2] [Hf1' Hf2'] [g1 Hg1] [g2 Hg2] [Hg1' Hg2']; cbn.
  now rewrite Hf1', Hf2', Hg1', Hg2'.
Defined.

#[refine]
#[export]
Instance Reloid_outl (X Y : Reloid) : ReloidHom (Reloid_product X Y) X :=
{
  func := SETOID_outl X Y
}.
Proof. now intros [] []; cbn. Defined.

#[refine]
#[export]
Instance Reloid_outr (X Y : Reloid) : ReloidHom (Reloid_product X Y) Y :=
{
  func := SETOID_outr X Y
}.
Proof. now intros [] []; cbn. Defined.

#[refine]
#[export]
Instance Reloid_fpair (X Y A : Reloid)
  (f : ReloidHom A X) (g : ReloidHom A Y)
  : ReloidHom A (Reloid_product X Y) :=
{
  func := SETOID_fpair f g
}.
Proof.
  now intros a1 a2 ra; cbn; split; apply pres_rel.
Defined.

#[refine]
#[export]
Instance HasProducts_Reloid : HasProducts ReloidCat :=
{
  product := Reloid_product;
  outl := Reloid_outl;
  outr := Reloid_outr;
  fpair := Reloid_fpair;
}.
Proof.
  now repeat split; cbn in *.
Defined.

#[refine]
#[export]
Instance Reloid_coproduct (X Y : Reloid) : Reloid :=
{
  carrier := SETOID_coproduct X Y;
  rel := relate_sum rel rel;
}.
Proof.
  now proper; destruct x, x0, y, y0; cbn in *; rewrite ?H, ?H0 in *.
Defined.

#[refine]
#[export]
Instance Reloid_finl (X Y : Reloid) : ReloidHom X (Reloid_coproduct X Y) :=
{
  func := SETOID_finl X Y;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance Reloid_finr (X Y : Reloid) : ReloidHom Y (Reloid_coproduct X Y) :=
{
  func := SETOID_finr X Y;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance Reloid_copair
  (X Y A : Reloid) (f : ReloidHom X A) (g : ReloidHom Y A)
  : ReloidHom (Reloid_coproduct X Y) A :=
{
  func := SETOID_copair f g
}.
Proof.
  now proper; destruct x, y; try apply pres_rel.
Defined.

#[refine]
#[export]
Instance HasCoproducts_Reloid : HasCoproducts ReloidCat :=
{
  coproduct := Reloid_coproduct;
  finl := Reloid_finl;
  finr := Reloid_finr;
  copair := Reloid_copair;
}.
Proof.
  split; cbn.
  - easy.
  - easy.
  - now intros P' h1 h2 HA HB [a | b]; cbn.
Defined.