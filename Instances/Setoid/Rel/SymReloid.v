Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.

Require Export Cat.Instances.Setoid.Rel.Reloid.

Set Implicit Arguments.

Class SymReloid : Type :=
{
    reloid : Reloid;
    rel_symmetric :> MySymmetric rel;
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
Instance SymReloidCat : Cat :=
{
    Ob := SymReloid;
    Hom := ReloidHom;
    HomSetoid := ReloidHomSetoid;
    comp := @ReloidComp;
    id := @ReloidId;
}.
Proof. all: sreloid. Defined.

#[refine]
Instance SymReloid_init : SymReloid :=
{
    reloid := Reloid_init;
}.
Proof. split. sreloid. Defined.

#[refine]
Instance SymReloid_create (X : SymReloid)
  : ReloidHom SymReloid_init X :=
{
    func := Reloid_create X
}.
Proof. sreloid. Defined.

#[refine]
Instance SymReloid_has_init : has_init SymReloidCat :=
{
    init := SymReloid_init;
    create := SymReloid_create
}.
Proof. sreloid. Defined.

#[refine]
Instance SymReloid_term : SymReloid :=
{
    reloid := Reloid_term;
}.
Proof. split. sreloid. Defined.

#[refine]
Instance SymReloid_delete (X : SymReloid)
  : ReloidHom X SymReloid_term :=
{
    func := Reloid_delete X
}.
Proof. sreloid. Defined.

#[refine]
Instance SymReloid_has_term : has_term SymReloidCat :=
{
    term := SymReloid_term;
    delete := SymReloid_delete;
}.
Proof. sreloid. Defined.

#[refine]
Instance SymReloid_prodOb (X Y : SymReloid) : SymReloid :=
{
    reloid := Reloid_prodOb X Y;
}.
Proof.
  split; cbn. destruct x, y, 1; split; cbn in *; apply symmetric; auto.
Defined.

#[refine]
Instance SymReloid_proj1 (X Y : SymReloid)
  : ReloidHom (SymReloid_prodOb X Y) X :=
{
    func := Reloid_proj1 X Y
}.
Proof. sreloid. Defined.

#[refine]
Instance SymReloid_proj2 (X Y : SymReloid)
  : ReloidHom (SymReloid_prodOb X Y) Y :=
{
    func := Reloid_proj2 X Y
}.
Proof. sreloid. Defined.

#[refine]
Instance SymReloid_fpair (X Y A : SymReloid)
  (f : ReloidHom A X) (g : ReloidHom A Y)
  : ReloidHom A (SymReloid_prodOb X Y) :=
{
    func := Reloid_fpair f g
}.
Proof. sreloid. Defined.

#[refine]
Instance SymReloid_has_products : has_products SymReloidCat :=
{
    prodOb := SymReloid_prodOb;
    proj1 := SymReloid_proj1;
    proj2 := SymReloid_proj2;
    fpair := SymReloid_fpair;
}.
Proof.
  all: unfold product_skolem; reloid.
Defined.

#[refine]
Instance SymReloid_coprodOb (X Y : SymReloid) : SymReloid :=
{
    reloid := Reloid_coprodOb X Y;
}.
Proof.
  split; cbn. destruct x, y; cbn; intros; intuition; apply symmetric; auto.
Defined.

#[refine]
Instance SymReloid_coproj1 (X Y : SymReloid)
  : ReloidHom X (SymReloid_coprodOb X Y) :=
{
    func := Reloid_coproj1 X Y;
}.
Proof. sreloid. Defined.

#[refine]
Instance SymReloid_coproj2 (X Y : SymReloid)
  : ReloidHom Y (SymReloid_coprodOb X Y) :=
{
    func := Reloid_coproj2 X Y;
}.
Proof. sreloid. Defined.

#[refine]
Instance SymReloid_copair (X Y A : SymReloid)
  (f : ReloidHom X A) (g : ReloidHom Y A)
  : ReloidHom (SymReloid_coprodOb X Y) A :=
{
    func := Reloid_copair f g
}.
Proof.
  proper. destruct x, y; try apply pres_rel; intuition eauto.
Defined.

#[refine]
Instance SymReloid_has_coproducts : has_coproducts SymReloidCat :=
{
    coprodOb := SymReloid_coprodOb;
    coproj1 := SymReloid_coproj1;
    coproj2 := SymReloid_coproj2;
    copair := SymReloid_copair;
}.
Proof.
  proper. destruct x1; rewrite ?H, ?H0; reflexivity.
  unfold coproduct_skolem. cat. destruct x; rewrite ?H, ?H0; reflexivity.
Defined.