From Cat Require Export Cat.
From Cat.Universal Require Import
  Initial Terminal Zero Product Coproduct IndexedProduct IndexedCoproduct.
From Cat Require Export Instances.Setoids.

Class SetoidRel (X Y : Setoid') : Type :=
{
  rel : X -> Y -> Prop;
  Proper_rel :> Proper (equiv ==> equiv ==> iff) rel
}.

Coercion rel : SetoidRel >-> Funclass.

Ltac setoidrelhom R := try intros until R;
match type of R with
| SetoidRel _ _ =>
  let a := fresh "Proper_" R in destruct R as [?R a]
| Hom _ _ => progress cbn in R; setoidrelhom R
end.

Ltac setoidrelhoms := intros; repeat
match goal with
| R : SetoidRel _ _ |- _ => setoidrelhom R
| f : Hom _ _ |- _ => setoidrelhom f
end.

Ltac rel' := repeat (intros;
match goal with
| |- Proper _ _ => proper
| |- Equivalence _ => solve_equiv
| |- context [match ?x with _ => _ end] => destruct x; auto
| _ : context [match ?x with _ => _ end] |- _ => destruct x; auto
| |- _ <-> _ => split; intros; my_simpl
| H : _ == _ |- _ => progress (rewrite H in *)
| H : forall _ _, _ <-> _ |- _ => edestruct H; clear H
| |- exists _, _ => eexists
end); cat.

Ltac setoidrel' := repeat (my_simpl || setoidobs || setoidrelhoms || cat).
Ltac setoidrel := try (setoidrel'; fail).

Ltac rel := repeat rel'; setoidrel'; rel'.

#[refine]
#[export]
Instance SetoidRel_Setoid (X Y : Setoid') : Setoid (SetoidRel X Y) :=
{
  equiv := fun (P Q : SetoidRel X Y) =>
    forall (x : X) (y : Y), P x y <-> Q x y
}.
Proof.
  now solve_equiv; intro; edestruct H; try edestruct H0; auto.
Defined.

#[refine]
#[export]
Instance SetoidRelComp
  (X Y Z : Setoid') (R : SetoidRel X Y) (S : SetoidRel Y Z) : SetoidRel X Z :=
{
  rel := fun (x : X) (z : Z) => exists y : Y, R x y /\ S y z
}.
Proof. now rel. Defined.

#[export]
Instance SetoidRelId (X : Setoid') : SetoidRel X X :=
{
  rel := equiv
}.

#[refine]
#[export]
Instance SetoidRelCat : Cat :=
{|
  Ob := Setoid';
  Hom := SetoidRel;
  HomSetoid := SetoidRel_Setoid;
  comp := SetoidRelComp;
  id := SetoidRelId
|}.
Proof. all: now rel. Defined.

#[export]
Program Instance HasInit_SetoidRel : HasInit SetoidRelCat :=
{
  init := CoqSetoid_init;
  create := fun X : Setoid' => {| rel := fun (e : Empty_set) _ => match e with end |}
}.
Next Obligation. easy. Defined.
Next Obligation. easy. Defined.

#[export]
Program Instance HasTerm_SetoidRel : HasTerm SetoidRelCat :=
{
  term := CoqSetoid_init;
  delete := fun X : Setoid' => {| rel := fun _ (e : Empty_set) => match e with end |}
}.
Next Obligation. easy. Defined.
Next Obligation. easy. Defined.

#[refine]
#[export]
Instance HasZero_SetoidRel : HasZero SetoidRelCat :=
{
  HasInit_HasZero := HasInit_SetoidRel;
  HasTerm_HasZero := HasTerm_SetoidRel
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance SetoidRel_product (X Y : Setoid') : Setoid' :=
{
  carrier := X + Y;
  setoid :=
  {|
    equiv := fun p1 p2 : X + Y =>
    match p1, p2 with
    | inl x, inl x' => @equiv _ X x x'
    | inr y, inr y' => @equiv _ Y y y'
    | _, _ => False
    end
  |}
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance SetoidRel_outl (X Y : Setoid') : SetoidRel (SetoidRel_product X Y) X :=
{
  rel := fun (p : X + Y) (x : X) =>
    match p with
    | inl x' => x == x'
    | _ => False
    end
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance SetoidRel_outr (X Y : Setoid') : SetoidRel (SetoidRel_product X Y) Y :=
{
  rel := fun (p : X + Y) (y : Y) =>
    match p with
    | inr y' => y == y'
    | _ => False
    end
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance SetoidRel_fpair
  (A B X : Setoid') (R : SetoidRel X A) (S : SetoidRel X B) : SetoidRel X (SetoidRel_product A B) :=
{
  rel := fun (x : X) (p : A + B) =>
    match p with
    | inl a => R x a
    | inr b => S x b
    end
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance HasProducts_SetoidRel : HasProducts SetoidRelCat :=
{
  product := SetoidRel_product;
  outl := SetoidRel_outl;
  outr := SetoidRel_outr;
  fpair := SetoidRel_fpair
}.
Proof.
  split; cbn.
  - intros Γ R S x y; split.
    + now intros [[] [r Heq]]; [rewrite Heq |].
    + now intros r; exists (inl y).
  - intros Γ R S x y; split.
    + now intros [[] [r Heq]]; [| rewrite Heq].
    + now intros s; exists (inr y).
  - intros Γ R S HeqR HeqS x [a | b]; split; setoidrel'; repeat
    match goal with
    | p : _ + _ |- _ => destruct p
    | H : False |- _ => inversion H
    end.
    + destruct (HeqR x a) as [[[y0_l | y0_r] [H'1 H'2]] _].
      * now exists (inl a).
      * eapply Proper_S; [| | eassumption]; easy.
      * easy.
    + destruct (HeqR x a) as [_ [[y0_l | y0_r] [H'1 H'2]]].
      * now exists (inl a).
      * eapply Proper_R; [| | eassumption]; easy.
      * easy.
    + destruct (HeqS x b) as [[[y0_l | y0_r] [H'1 H'2]] _].
      * now exists (inr b).
      * easy.
      * eapply Proper_S; [| | eassumption]; easy.
    + destruct (HeqS x b) as [_ [[y0_l | y0_r] [H'1 H'2]]].
      * now exists (inr b).
      * easy.
      * eapply Proper_R; [| | eassumption]; easy.
Defined.

Definition SetoidRel_coproduct := SetoidRel_product.

#[refine]
#[export]
Instance SetoidRel_finl (X Y : Setoid') : SetoidRel X (SetoidRel_coproduct X Y) :=
{
  rel := fun (x : X) (p : X + Y) =>
    match p with
    | inl x' => x == x'
    | _ => False
    end
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance SetoidRel_finr (X Y : Setoid') : SetoidRel Y (SetoidRel_coproduct X Y) :=
{
  rel := fun (y : Y) (p : X + Y) =>
    match p with
    | inr y' => y == y'
    | _ => False
    end
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance SetoidRel_copair
  (A B X : Setoid') (R : SetoidRel A X) (S : SetoidRel B X)
  : SetoidRel (SetoidRel_coproduct A B) X :=
{
  rel := fun (p : A + B) (x : X) =>
    match p with
    | inl a => R a x
    | inr b => S b x
    end
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance HasCoproducts_SetoidRel : HasCoproducts SetoidRelCat :=
{
  coproduct := SetoidRel_coproduct;
  finl := SetoidRel_finl;
  finr := SetoidRel_finr;
  copair := SetoidRel_copair;
}.
Proof.
  split; setoidrel'; repeat
  match goal with
  | p : _ + _ |- _ => destruct p
  | H : False |- _ => inversion H
  end.
  - now eapply Proper_f; eauto.
  - now exists (inl x).
  - now eapply Proper_g; eauto.
  - now exists (inr x).
  - destruct (H a y) as [[[y0_l | y0_r] [H'1 H'2]] _].
    + now exists (inl a).
    + now eapply Proper_h2; eauto.
    + easy.
  - destruct (H0 b y) as [[[y0_l | y0_r] [H'1 H'2]] _].
    + now exists (inr b).
    + easy.
    + now eapply Proper_h2; eauto.
  - destruct (H a y) as [_ [[y0_l | y0_r] [H'1 H'2]]].
    + now exists (inl a).
    + now eapply Proper_h1; eauto.
    + easy.
  - destruct (H0 b y) as [_ [[y0_l | y0_r] [H'1 H'2]]].
    + now exists (inr b).
    + easy.
    + now eapply Proper_h1; eauto.
Defined.