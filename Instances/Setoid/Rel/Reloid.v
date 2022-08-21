From Cat Require Export Cat.
From Cat.Limits Require Import Initial Terminal Product Coproduct.
From Cat.Limits.Indexed Require Import Product Coproduct.
From Cat Require Export Instances.Setoids.

Set Implicit Arguments.

Class Reloid : Type :=
{
  carrier : Setoid';
  rel : carrier -> carrier -> Prop;
  Proper_rel :> Proper (equiv ==> equiv ==> iff) rel
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
Proof. solve_equiv. Defined.

#[refine]
#[export]
Instance ReloidComp {X Y Z : Reloid} (f : ReloidHom X Y) (g : ReloidHom Y Z) : ReloidHom X Z :=
{
  func := SetoidComp f g
}.
Proof. reloid. Defined.

#[refine]
#[export]
Instance ReloidId (X : Reloid) : ReloidHom X X :=
{
  func := SetoidId X
}.
Proof. reloid. Defined.

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
Proof. all: reloid. Defined.

#[refine]
#[export]
Instance Reloid_init : Reloid :=
{
  carrier := CoqSetoid_init;
  rel := fun _ _ => True
}.
Proof. now proper. Defined.

#[refine]
#[export]
Instance Reloid_create (X : Reloid) : ReloidHom Reloid_init X :=
{
  func := CoqSetoid_create X
}.
Proof. proper. destruct x. Defined.

#[refine]
#[export]
Instance HasInit_Reloid : HasInit ReloidCat :=
{
  init := Reloid_init;
  create := Reloid_create
}.
Proof. reloid. Defined.

#[export]
Instance Reloid_term : Reloid :=
{
  carrier := CoqSetoid_term;
  rel := fun _ _ => True
}.

#[refine]
#[export]
Instance Reloid_delete (X : Reloid) : ReloidHom X Reloid_term :=
{
  func := CoqSetoid_delete X
}.
Proof. proper. Defined.

#[refine]
#[export]
Instance HasTerm_Reloid : HasTerm ReloidCat :=
{
  term := Reloid_term;
  delete := Reloid_delete;
}.
Proof. reloid. Defined.

#[refine]
#[export]
Instance Reloid_prodOb (X Y : Reloid) : Reloid :=
{
  carrier := CoqSetoid_prodOb X Y;
  rel := fun p p' => @rel X (fst p) (fst p') /\ @rel Y (snd p) (snd p')
}.
Proof.
  proper. destruct H, H0. now rewrite H, H0, H1, H2.
Defined.

#[refine]
#[export]
Instance Reloid_outl (X Y : Reloid) : ReloidHom (Reloid_prodOb X Y) X :=
{
  func := CoqSetoid_outl X Y
}.
Proof. reloid. Defined.

#[refine]
#[export]
Instance Reloid_outr (X Y : Reloid) : ReloidHom (Reloid_prodOb X Y) Y :=
{
  func := CoqSetoid_outr X Y
}.
Proof. reloid. Defined.

#[refine]
#[export]
Instance Reloid_fpair (X Y A : Reloid)
  (f : ReloidHom A X) (g : ReloidHom A Y)
  : ReloidHom A (Reloid_prodOb X Y) :=
{
  func := CoqSetoid_fpair f g
}.
Proof. reloid. Defined.

#[refine]
#[export]
Instance HasProducts_Reloid : HasProducts ReloidCat :=
{
  prodOb := Reloid_prodOb;
  outl := Reloid_outl;
  outr := Reloid_outr;
  fpair := Reloid_fpair;
}.
Proof.
  all: unfold isProduct; reloid.
Defined.

#[refine]
#[export]
Instance Reloid_coprodOb (X Y : Reloid) : Reloid :=
{
  carrier := CoqSetoid_coprodOb X Y;
  rel := fun p p' =>
  match p, p' with
  | inl x, inl x' => rel x x'
  | inr y, inr y' => rel y y'
  | _, _ => False
  end
}.
Proof.
  proper. destruct x, x0, y, y0; intuition eauto;
  rewrite <- ?H, <- ?H0; auto; rewrite ?H, ?H0; auto.
Defined.

#[refine]
#[export]
Instance Reloid_finl (X Y : Reloid) : ReloidHom X (Reloid_coprodOb X Y) :=
{
  func := CoqSetoid_finl X Y;
}.
Proof. reloid. Defined.

#[refine]
#[export]
Instance Reloid_finr (X Y : Reloid) : ReloidHom Y (Reloid_coprodOb X Y) :=
{
  func := CoqSetoid_finr X Y;
}.
Proof. reloid. Defined.

#[refine]
#[export]
Instance Reloid_copair
  (X Y A : Reloid) (f : ReloidHom X A) (g : ReloidHom Y A)
  : ReloidHom (Reloid_coprodOb X Y) A :=
{
  func := CoqSetoid_copair f g
}.
Proof.
  proper. destruct x, y; try apply pres_rel; intuition eauto.
Defined.

#[refine]
#[export]
Instance HasCoproducts_Reloid : HasCoproducts ReloidCat :=
{
  coprodOb := Reloid_coprodOb;
  finl := Reloid_finl;
  finr := Reloid_finr;
  copair := Reloid_copair;
}.
Proof.
  proper. now destruct x1; rewrite ?H, ?H0.
  unfold isCoproduct. cat. now destruct x; rewrite ?H, ?H0.
Defined.