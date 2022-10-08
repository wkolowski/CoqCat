From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct.
From Cat Require Export Instances.SETOID.

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
| Ob _ => progress cbn in X; graphob X
end; cbn in *.

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
| Hom _ _ => progress cbn in f; graphhom f
end; cbn in *.

Ltac graphhoms := intros; repeat
match goal with
| f : GraphHom _ _ |- _ => graphhom f
| f : Hom _ _ |- _ => graphhom f
| _ => idtac
end.

Ltac graph' := repeat (graphobs || graphhoms || cat).
Ltac graph := try (graph'; fail).

#[refine]
#[export]
Instance GraphHomSetoid (X Y : Graph) : Setoid (GraphHom X Y) :=
{
  equiv := fun f g : GraphHom X Y =>
    (forall v : vertices X, fver f v == fver g v)
      /\
    (forall e : edges X, fed f e == fed g e)
}.
Proof.
  now solve_equiv; intro; rewrite ?H, ?H2, ?H0, ?H1.
Defined.

#[refine]
#[export]
Instance GraphComp (X Y Z : Graph) (f : GraphHom X Y) (g : GraphHom Y Z) : GraphHom X Z :=
{
  fver := SetoidComp (fver f) (fver g);
  fed := SetoidComp (fed f) (fed g);
}.
Proof.
  - now cbn; intros; rewrite !pres_src.
  - now cbn; intros; rewrite !pres_tgt.
Defined.

#[refine]
#[export]
Instance GraphId (X : Graph) : GraphHom X X :=
{
  fver := SetoidId (vertices X);
  fed := SetoidId (edges X);
}.
Proof. all: easy. Defined.

#[refine]
#[export]
Instance GraphCat : Cat :=
{
  Ob := Graph;
  Hom := GraphHom;
  HomSetoid := GraphHomSetoid;
  comp := GraphComp;
  id := GraphId;
}.
Proof.
  - intros A B C f f' [Hf1 Hf2] g g' [Hg1 Hg2]; cbn in *.
    split; intros.
    + now rewrite Hf1, Hg1.
    + now rewrite Hf2, Hg2.
  - now cbn.
  - now cbn.
  - now cbn.
Defined.

(** Now we define the free category for the given graph G. *)

(** Morphisms are finite walks. *)
Inductive Walk {G : Graph} : vertices G -> vertices G -> Type :=
| Stop : forall v : vertices G, Walk v v
| Step :
  forall {v1 v2 v3 : vertices G} {e : edges G},
    src e = v1 -> tgt e = v2 -> Walk v2 v3 -> Walk v1 v3.

Arguments Stop {G v}.
Arguments Step {G v1 v2 v3 e} _ _ _.

Fixpoint wapp
  {G : Graph} {v1 v2 v3 : vertices G}
  (w1 : Walk v1 v2) : Walk v2 v3 -> Walk v1 v3 :=
match w1 with
| Stop => fun w2 => w2
| Step p1 p2 w1' => fun w2 => Step p1 p2 (wapp w1' w2)
end.

#[refine]
#[export]
Instance FreeCat (G : Graph) : Cat :=
{
  Ob := vertices G;
  Hom := Walk;
  id := @Stop G;
  comp := @wapp G;
}.
Proof.
  - intros v1 v2.
    split with (fun w1 w2 => w1 = w2).
    now split; red; [| | apply transitivity].
  - now intros v1 v2 v3 w12 w12' <- w23 w23' <-; cbn.
  - induction f as [| v1 v2 v3 e p1 p2 f']; cbn; intros.
    + easy.
    + now rewrite IHf'.
  - now cbn.
  - induction f as [| v1 v2 v3 e p1 p2 f']; cbn.
    + easy.
    + now rewrite IHf'.
Defined.