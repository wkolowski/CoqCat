Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Class Graph : Type :=
{
    vertices : Type;
    edges : Type;
    src : edges -> vertices;
    tgt : edges -> vertices;
}.

Arguments vertices _ : clear implicits.
Arguments edges _ : clear implicits.

Ltac graphob X := try intros until X;
match type of X with
  | Graph => 
    let a := fresh X "_V" in
    let b := fresh X "_E" in
    let c := fresh X "_src" in
    let d := fresh X "_tgt" in destruct X as [a b c d]
  | Ob _ => progress simpl in X; graphob X
end; simpl in *.

Ltac graphobs := repeat
match goal with
  | X : Graph |- _ => graphob X
  | X : Ob _ |- _ => graphob X
end.

Class GraphHom (X Y : Graph) : Type :=
{
    fver : vertices X -> vertices Y;
    fed : edges X -> edges Y;
    pres_src : forall e : edges X, src (fed e) = fver (src e);
    pres_tgt : forall e : edges X, tgt (fed e) = fver (tgt e);
}.

Arguments fver [X] [Y] _ _.
Arguments fed [X] [Y] _ _.

Ltac graphhom f := try intros until f;
match type of f with
  | GraphHom _ _ =>
      let a := fresh f "_fver" in
      let b := fresh f "_fed" in
      let c := fresh f "_pres_src" in
      let d := fresh f "_pres_tgt" in destruct f as [a b c d]
  | Hom _ _ => progress simpl in f; graphhom f
end; simpl in *.

Ltac graphhoms := intros; repeat
match goal with
  | f : GraphHom _ _ |- _ => graphhom f
  | f : Hom _ _ |- _ => graphhom f
  | _ => idtac
end.

Ltac graph' := repeat (graphobs || graphhoms || cat).
Ltac graph := try (graph'; fail).

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
  all: graphhoms; repeat
  match goal with
      | H : forall _, _ = _ |- _ => try rewrite H; clear H
  end; auto.
Defined.

Instance GraphId (X : Graph) : GraphHom X X :=
{
    fver := fun v : vertices X => v;
    fed := fun e : edges X => e
}.
Proof. all: graph. Defined.

Instance GraphCat : Cat :=
{
    Ob := Graph;
    Hom := GraphHom;
    HomSetoid := GraphHomSetoid;
    comp := GraphComp;
    id := GraphId;
}.
Proof.
  all: graph. proper. split; intros; repeat
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