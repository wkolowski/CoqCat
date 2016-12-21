Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".
Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/Instances".

Require Import NPeano.

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Require Export Pros.

Set Universe Polymorphism.

Class Pos : Type :=
{
    pros : Pros;
    leq_antisym : forall x y : carrier, x ≤ y /\ y ≤ x -> x = y
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

Ltac posob' P := posob P; prosob P.

Ltac posobs_template tac := intros; repeat
match goal with
  | P : Pos |- _ => tac P
  | P : Ob _ |- _ => tac P
end.

Ltac posobs := posobs_template posob.
Ltac posobs' := posobs_template posob'.

Notation "'PosHom' X Y" := (ProsHom X Y) (at level 40, only parsing).

Ltac pos' := repeat (pos_simpl; try proshoms; try posobs).
Ltac pos := try (pos'; fail).

(*Definition PosComp := ProsComp.

Definition PosId := ProsId.*)

Instance PosCat : Cat :=
{
    Ob := Pos;
    Hom := ProsHom;
    HomSetoid := @HomSetoid ProsCat;
    comp := ProsComp;
    id := ProsId
}.
Proof.
  (* Proper *) pos'. rewrite H, H0. auto.
  (* Category laws *) all: pos.
Defined.

Instance Pos_init : Pos :=
{
    pros := Pros_init
}.
Proof. destruct x. Defined.

Instance Pos_has_init : has_init PosCat :=
{
    init := Pos_init;
    create := Pros_create
}.
Proof. pros. Defined.

Instance Pos_term : Pos :=
{
    pros := Pros_term
}.
Proof. cat. Defined.

Instance Pos_has_term : has_term PosCat :=
{
    term := Pos_term;
    delete := Pros_delete
}.
Proof. pros. Defined.

Instance Pos_prod (X Y : Pos) : Pos :=
{
    pros := Pros_prod X Y
}.
Proof. pos'. destruct x, y. cat. f_equal; auto. Defined.

Instance Pos_has_products : has_products PosCat :=
{
    prodOb := Pos_prod;
    proj1 := Pros_proj1;
    proj2 := Pros_proj2;
    diag := @Pros_diag
}.
Proof. pos'. cat. rewrite H, H0. destruct (y x); auto. Defined.