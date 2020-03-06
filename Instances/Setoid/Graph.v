Require Export Cat.
Require Import Limits.InitTerm.
Require Import Limits.BinProdCoprod.

Require Export Setoids.

Set Implicit Arguments.

Class Graph : Type :=
{
    vertices : Setoid';
    edges : Setoid';
    src : SetoidHom edges vertices;
    tgt : SetoidHom edges vertices;
}.

Coercion vertices : Graph >-> Setoid'.

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
    fver: SetoidHom (vertices X) (vertices Y);
    fed : SetoidHom (edges X) (edges Y);
    pres_src : forall e : edges X, src (fed e) == fver (src e);
    pres_tgt : forall e : edges X, tgt (fed e) == fver (tgt e);
}.

Arguments fver [X Y] _.
Arguments fed [X Y] _.

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

#[refine]
Instance GraphHomSetoid (X Y : Graph) : Setoid (GraphHom X Y) :=
{
    equiv := fun f g : GraphHom X Y =>
      (forall v : vertices X, fver f v == fver g v) /\
      (forall e : edges X, fed f e == fed g e)
}.
Proof.
  solve_equiv; intro; rewrite ?H, ?H2, ?H0, ?H1; try reflexivity.
Defined.

#[refine]
Instance GraphComp (X Y Z : Graph)
    (f : GraphHom X Y) (g : GraphHom Y Z) : GraphHom X Z :=
{
    fver := SetoidComp (fver f) (fver g);
    fed := SetoidComp (fed f) (fed g);
}.
Proof.
  all: cbn; graphhoms; repeat
  match goal with
      | H : forall _, _ = _ |- _ => try rewrite H; clear H
  end.
    rewrite g_pres_src, f_pres_src. reflexivity.
    rewrite g_pres_tgt, f_pres_tgt. reflexivity.
Defined.

#[refine]
Instance GraphId (X : Graph) : GraphHom X X :=
{
    fver := SetoidId (vertices X);
    fed := SetoidId (edges X);
}.
Proof. all: graph. Defined.

#[refine]
Instance GraphCat : Cat :=
{
    Ob := Graph;
    Hom := GraphHom;
    HomSetoid := GraphHomSetoid;
    comp := GraphComp;
    id := GraphId;
}.
Proof.
  proper. my_simpl; intros; rewrite ?H, ?H0, ?H1, ?H2; reflexivity.
  all: graph.
Defined.

(* These are only finite paths *)
Inductive path {G : Graph} : vertices G -> vertices G -> Type :=
    | idpath : forall v : vertices G,
        path v v
    | edgepath : forall (v1 v2 v3 : vertices G) (e : edges G),
        path v1 v2 -> src e = v2 -> tgt e = v3 -> path v1 v3.

(* TODO: define free category *)