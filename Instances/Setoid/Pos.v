From Cat Require Export Cat.
From Cat.Limits Require Export Initial Terminal Product Coproduct.
From Cat Require Export Instances.Setoid.Pros.

Class Pos : Type :=
{
  pros :> Pros;
  leq_antisym : forall x y : carrier, x ≤ y -> y ≤ x -> x == y
}.

#[global] Hint Resolve leq_antisym : core.

Coercion pros : Pos >-> Pros.

Ltac pos_simpl := pros_simpl.

Ltac posob P := try intros until P;
match type of P with
| Pos =>
  let a := fresh P "_leq_antisym" in destruct P as [P a]
| Ob _ => progress cbn in P; prosob P
end.

Ltac posob' P := posob P; prosob' P.

Ltac posobs_template tac := intros; repeat
match goal with
| P : Pos |- _ => tac P
| P : Ob _ |- _ => tac P
end.

Ltac posobs := posobs_template posob.
Ltac posobs' := posobs_template posob'.

Notation "'PosHom' X Y" := (ProsHom X Y) (at level 40).

Ltac pos' := repeat (pos_simpl || proshoms || posobs || pros').
Ltac pos := try (pos'; fail).

#[refine]
#[export]
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
#[export]
Instance Pos_init : Pos :=
{
  pros := Pros_init
}.
Proof. pos. Defined.

#[refine]
#[export]
Instance HasInit_Pos : HasInit PosCat :=
{
  init := Pos_init;
  create := Pros_create
}.
Proof. pos. Defined.

#[refine]
#[export]
Instance Pos_term : Pos :=
{
  pros := Pros_term
}.
Proof. pos. Defined.

#[refine]
#[export]
Instance HasTerm_Pos : HasTerm PosCat :=
{
  term := Pos_term;
  delete := Pros_delete
}.
Proof. pos. Defined.

#[refine]
#[export]
Instance Pos_product (X Y : Pos) : Pos :=
{
  pros := Pros_product X Y
}.
Proof. pos. Defined.

#[refine]
#[export]
Instance HasProducts_Pos : HasProducts PosCat :=
{
  product := Pos_product;
  outl := Pros_outl;
  outr := Pros_outr;
  fpair := @Pros_fpair
}.
Proof.
  proper.
  all: pos.
Defined.

#[refine]
#[export]
Instance Pos_coproduct (X Y : Pos) : Pos :=
{
  pros := Pros_coproduct X Y;
}.
Proof.
  destruct x, y; pos.
Defined.

Definition Pos_finl (X Y : Pos) : ProsHom X (Pos_coproduct X Y).
Proof.
  red. exists (Pros_finl X Y). pos.
Defined.

Definition Pos_finr (X Y : Pos) : ProsHom Y (Pos_coproduct X Y).
Proof.
  red. exists (Pros_finr X Y). pos.
Defined.

Definition Pos_copair
  (A B X : Pos) (f : ProsHom A X) (g : ProsHom B X) : ProsHom (Pos_coproduct A B) X.
Proof.
  red. exists (Pros_copair f g). destruct a, a'; pos.
Defined.

#[refine]
#[export]
Instance HasCoproducts_Pos : HasCoproducts PosCat :=
{
  coproduct := Pos_coproduct;
  finl := Pos_finl;
  finr := Pos_finr;
  copair := Pos_copair
}.
Proof.
  proper. destruct x1; proper.
  repeat split; cbn.
    1-2: easy.
    destruct x; pos.
Defined.