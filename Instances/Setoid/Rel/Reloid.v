Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.

Require Export Cat.Instances.Setoids.

Set Implicit Arguments.

Class Reloid : Type :=
{
    carrier : Setoid';
    rel : carrier -> carrier -> Prop;
    rel_Proper :> Proper (equiv ==> equiv ==> iff) rel
}.

Coercion carrier : Reloid >-> Setoid'.

Ltac reloidob X := try intros until X;
match type of X with
  | Reloid =>
    let a := fresh X "_rel" in 
    let b := fresh X "_rel_Proper" in destruct X as [X a b]; setoidob X
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
Instance ReloidHomSetoid (X Y : Reloid) : Setoid (ReloidHom X Y) :=
{
    equiv := fun f g => forall x : X, f x == g x
}.
Proof. solve_equiv. Defined.

#[refine]
Instance ReloidComp {X Y Z : Reloid} (f : ReloidHom X Y) (g : ReloidHom Y Z)
  : ReloidHom X Z :=
{
    func := SetoidComp f g
}.
Proof. reloid. Defined.

#[refine]
Instance ReloidId (X : Reloid) : ReloidHom X X :=
{
    func := SetoidId X
}.
Proof. reloid. Defined.

#[refine]
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
Instance Reloid_init : Reloid :=
{
    carrier := CoqSetoid_init;
    rel := fun _ _ => True
}.
Proof. proper. reflexivity. Defined.

#[refine]
Instance Reloid_create (X : Reloid) : ReloidHom Reloid_init X :=
{
    func := CoqSetoid_create X
}.
Proof. proper. destruct x. Defined.

#[refine]
Instance Reloid_has_init : has_init ReloidCat :=
{
    init := Reloid_init;
    create := Reloid_create
}.
Proof. reloid. Defined.

Instance Reloid_term : Reloid :=
{
    carrier := CoqSetoid_term;
    rel := fun _ _ => True
}.

#[refine]
Instance Reloid_delete (X : Reloid) : ReloidHom X Reloid_term :=
{
    func := CoqSetoid_delete X
}.
Proof. proper. Defined.

#[refine]
Instance Reloid_has_term : has_term ReloidCat :=
{
    term := Reloid_term;
    delete := Reloid_delete;
}.
Proof. reloid. Defined.

#[refine]
Instance Reloid_prodOb (X Y : Reloid) : Reloid :=
{
    carrier := CoqSetoid_prodOb X Y;
    rel := fun p p' => @rel X (fst p) (fst p') /\ @rel Y (snd p) (snd p')
}.
Proof.
  proper. destruct H, H0. rewrite H, H0, H1, H2. reflexivity.
Defined.

#[refine]
Instance Reloid_proj1 (X Y : Reloid) : ReloidHom (Reloid_prodOb X Y) X :=
{
    func := CoqSetoid_proj1 X Y
}.
Proof. reloid. Defined.

#[refine]
Instance Reloid_proj2 (X Y : Reloid) : ReloidHom (Reloid_prodOb X Y) Y :=
{
    func := CoqSetoid_proj2 X Y
}.
Proof. reloid. Defined.

#[refine]
Instance Reloid_fpair (X Y A : Reloid)
  (f : ReloidHom A X) (g : ReloidHom A Y)
  : ReloidHom A (Reloid_prodOb X Y) :=
{
    func := CoqSetoid_fpair f g
}.
Proof. reloid. Defined.

#[refine]
Instance Reloid_has_products : has_products ReloidCat :=
{
    prodOb := Reloid_prodOb;
    proj1 := Reloid_proj1;
    proj2 := Reloid_proj2;
    fpair := Reloid_fpair;
}.
Proof.
  all: unfold product_skolem; reloid.
Defined.

#[refine]
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
Instance Reloid_coproj1 (X Y : Reloid)
  : ReloidHom X (Reloid_coprodOb X Y) :=
{
    func := CoqSetoid_coproj1 X Y;
}.
Proof. reloid. Defined.

#[refine]
Instance Reloid_coproj2 (X Y : Reloid)
  : ReloidHom Y (Reloid_coprodOb X Y) :=
{
    func := CoqSetoid_coproj2 X Y;
}.
Proof. reloid. Defined.

#[refine]
Instance Reloid_copair (X Y A : Reloid)
  (f : ReloidHom X A) (g : ReloidHom Y A)
  : ReloidHom (Reloid_coprodOb X Y) A :=
{
    func := CoqSetoid_copair f g
}.
Proof.
  proper. destruct x, y; try apply pres_rel; intuition eauto.
Defined.

#[refine]
Instance Reloid_has_coproducts : has_coproducts ReloidCat :=
{
    coprodOb := Reloid_coprodOb;
    coproj1 := Reloid_coproj1;
    coproj2 := Reloid_coproj2;
    copair := Reloid_copair;
}.
Proof.
  proper. destruct x1; rewrite ?H, ?H0; reflexivity.
  unfold coproduct_skolem. cat. destruct x; rewrite ?H, ?H0; reflexivity.
Defined.