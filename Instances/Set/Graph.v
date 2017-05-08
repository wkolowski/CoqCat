Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

(* TODO : define appropriate tactics *)
Class Graph : Type :=
{
    vertices : Type;
    edges : Type;
    src : edges -> vertices;
    tgt : edges -> vertices;
}.

Arguments vertices _ : clear implicits.
Arguments edges _ : clear implicits.

Class GraphHom (X Y : Graph) : Type :=
{
    fver : vertices X -> vertices Y;
    fed : edges X -> edges Y;
    pres_src : forall e : edges X, src (fed e) = fver (src e);
    pres_tgt : forall e : edges X, tgt (fed e) = fver (tgt e);
}.

Arguments fver [X] [Y] _ _.
Arguments fed [X] [Y] _ _.

Instance GraphHomSetoid (X Y : Graph) : Setoid (GraphHom X Y) :=
{
    equiv := fun f g : GraphHom X Y =>
      (forall v : vertices X, fver f v = fver g v) /\
      (forall e : edges X, fed f e = fed g e)
}.
Proof.
  do 2 (split; try red; intros); repeat
  match reverse goal with
      | H : _ /\ _ |- _ => destruct H
      | H : forall _, _ = _ |- _ => try rewrite H; clear H
  end; auto.
Defined.

Instance GraphComp (X Y Z : Graph)
    (f : GraphHom X Y) (g : GraphHom Y Z) : GraphHom X Z :=
{
    fver := fun v : vertices X => fver g (fver f v);
    fed := fun e : edges X => fed g (fed f e);
}.
Proof.
  all: intros; destruct X, Y, Z, f, g; simpl in *;
  repeat match goal with
      | H : forall _, _ = _ |- _ => try rewrite H; clear H
  end; auto.
Defined.

Instance GraphId (X : Graph) : GraphHom X X :=
{
    fver := fun v : vertices X => v;
    fed := fun e : edges X => e
}.
Proof. all: cat. Defined.

Instance GraphCat : Cat :=
{
    Ob := Graph;
    Hom := GraphHom;
    HomSetoid := GraphHomSetoid;
    comp := GraphComp;
    id := GraphId;
}.
Proof.
  all: cat. proper. split; intros; repeat
  match reverse goal with
      | H : _ /\ _ |- _ => destruct H
      | H : forall _, _ = _ |- _ => try rewrite H; clear H
  end; auto.
Defined.

(* These are only finite paths *)
Inductive path {G : Graph} : vertices G -> vertices G -> Type :=
    | idpath : forall v : vertices G,
        path v v
    | edgepath : forall (v1 v2 v3 : vertices G) (e : edges G),
        path v1 v2 -> src e = v2 -> tgt e = v3 -> path v1 v3.

(* TODO: define free category *)