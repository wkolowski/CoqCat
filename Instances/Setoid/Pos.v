Require Import NPeano.

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Require Export Instances.Setoid.Pros.

Class Pos : Type :=
{
    pros :> Pros;
    leq_antisym : forall x y : carrier, x ≤ y -> y ≤ x -> x == y
}.

Hint Resolve leq_antisym.

Coercion pros : Pos >-> Pros.

Ltac pos_simpl := pros_simpl.

Ltac posob P := try intros until P;
match type of P with
  | Pos =>
    let a := fresh P "_leq_antisym" in destruct P as [P a]
  | Ob _ => progress simpl in P; prosob P
end.

Ltac posob' P := posob P; prosob' P.

Ltac posobs_template tac := intros; repeat
match goal with
  | P : Pos |- _ => tac P
  | P : Ob _ |- _ => tac P
end.

Ltac posobs := posobs_template posob.
Ltac posobs' := posobs_template posob'.

Notation "'PosHom' X Y" := (ProsHom X Y) (at level 40). (*, only parsing).*)

Ltac pos' := repeat (pos_simpl || proshoms || posobs || pros').
Ltac pos := try (pos'; fail).

#[refine]
Instance PosCat : Cat :=
{
    Ob := Pos;
    Hom := ProsHom;
    HomSetoid := @HomSetoid ProsCat;
    comp := ProsComp;
    id := ProsId
}.
Proof.
  (* Proper *) proper. pos'.
  (* Category laws *) all: pos.
Defined.

#[refine]
Instance Pos_init : Pos :=
{
    pros := Pros_init
}.
Proof. pos. Defined.

#[refine]
Instance Pos_has_init : has_init PosCat :=
{
    init := Pos_init;
    create := Pros_create
}.
Proof. pos. Defined.

#[refine]
Instance Pos_term : Pos :=
{
    pros := Pros_term
}.
Proof. pos. Defined.

#[refine]
Instance Pos_has_term : has_term PosCat :=
{
    term := Pos_term;
    delete := Pros_delete
}.
Proof. pos. Defined.

#[refine]
Instance Pos_prodOb (X Y : Pos) : Pos :=
{
    pros := Pros_prodOb X Y
}.
Proof. pos. Defined.

#[refine]
Instance Pos_has_products : has_products PosCat :=
{
    prodOb := Pos_prodOb;
    proj1 := Pros_proj1;
    proj2 := Pros_proj2;
    fpair := @Pros_fpair
}.
Proof.
  proper.
  all: pos.
Defined.

#[refine]
Instance Pos_coprodOb (X Y : Pos) : Pos :=
{
    pros := Pros_coprodOb X Y;
}.
Proof.
  destruct x, y; pos.
Defined.

Definition Pos_coproj1 (X Y : Pos) :
    ProsHom X (Pos_coprodOb X Y).
Proof.
  red. exists (Pros_coproj1 X Y). pos.
Defined.

Definition Pos_coproj2 (X Y : Pos) :
    ProsHom Y (Pos_coprodOb X Y).
Proof.
  red. exists (Pros_coproj2 X Y). pos.
Defined.

Definition Pos_copair (A B X : Pos) (f : ProsHom A X) (g : ProsHom B X)
    : ProsHom (Pos_coprodOb A B) X.
Proof.
  red. exists (Pros_copair f g). destruct a, a'; pos.
Defined.

#[refine]
Instance Pos_has_coproducts : has_coproducts PosCat :=
{
    coprodOb := Pos_coprodOb;
    coproj1 := Pos_coproj1;
    coproj2 := Pos_coproj2;
    copair := Pos_copair
}.
Proof.
  proper. destruct x1; proper.
  repeat split; simpl; try reflexivity.
    destruct x; pos.
Defined.