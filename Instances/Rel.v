From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Zero Product Coproduct.
From Cat Require Export Instances.SETOID.

Class RelHom (X Y : Setoid') : Type :=
{
  rel : X -> Y -> Prop;
  Proper_rel :> Proper (equiv ==> equiv ==> iff) rel
}.

Coercion rel : RelHom >-> Funclass.

Ltac relhom R := try intros until R;
match type of R with
| RelHom _ _ =>
  let a := fresh "Proper_" R in destruct R as [?R a]
| Hom _ _ => progress cbn in R; relhom R
end.

Ltac relhoms := intros; repeat
match goal with
| R : RelHom _ _ |- _ => relhom R
| f : Hom _ _ |- _ => relhom f
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

Ltac setoidrel' := repeat (my_simpl || setoidobs || relhoms || cat).
Ltac setoidrel := try (setoidrel'; fail).

Ltac rel := repeat rel'; setoidrel'; rel'.

#[refine]
#[export]
Instance RelHom_Setoid (X Y : Setoid') : Setoid (RelHom X Y) :=
{
  equiv := fun (P Q : RelHom X Y) =>
    forall (x : X) (y : Y), P x y <-> Q x y
}.
Proof.
  now solve_equiv; intro; edestruct H; try edestruct H0; auto.
Defined.

#[refine]
#[export]
Instance RelHomComp
  (X Y Z : Setoid') (R : RelHom X Y) (S : RelHom Y Z) : RelHom X Z :=
{
  rel := fun (x : X) (z : Z) => exists y : Y, R x y /\ S y z
}.
Proof. now rel. Defined.

#[export]
Instance RelHomId (X : Setoid') : RelHom X X :=
{
  rel := equiv
}.

#[refine]
#[export]
Instance Rel : Cat :=
{|
  Ob := Setoid';
  Hom := RelHom;
  HomSetoid := RelHom_Setoid;
  comp := RelHomComp;
  id := RelHomId;
|}.
Proof. all: now rel. Defined.

#[export]
Program Instance HasInit_Rel : HasInit Rel :=
{
  init   := SETOID_init;
  create := fun X : Setoid' => {| rel := fun (e : Empty_set) _ => match e with end |};
}.
Next Obligation. easy. Defined.
Next Obligation. easy. Defined.

#[export]
Program Instance HasTerm_Rel : HasTerm Rel :=
{
  term   := SETOID_init;
  delete := fun X : Setoid' => {| rel := fun _ (e : Empty_set) => match e with end |};
}.
Next Obligation. easy. Defined.
Next Obligation. easy. Defined.

#[refine]
#[export]
Instance HasZero_Rel : HasZero Rel :=
{
  HasInit_HasZero := HasInit_Rel;
  HasTerm_HasZero := HasTerm_Rel;
}.
Proof. easy. Defined.

#[export]
Instance Rel_product (X Y : Setoid') : Setoid' :=
{
  carrier := X + Y;
  setoid  := Setoid_sum X Y;
}.

#[refine]
#[export]
Instance Rel_outl (X Y : Setoid') : RelHom (Rel_product X Y) X :=
{
  rel := fun (p : X + Y) (x : X) =>
    match p with
    | inl x' => x == x'
    | _ => False
    end;
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance Rel_outr (X Y : Setoid') : RelHom (Rel_product X Y) Y :=
{
  rel := fun (p : X + Y) (y : Y) =>
    match p with
    | inr y' => y == y'
    | _ => False
    end;
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance Rel_fpair
  (A B X : Setoid') (R : RelHom X A) (S : RelHom X B) : RelHom X (Rel_product A B) :=
{
  rel := fun (x : X) (p : A + B) =>
    match p with
    | inl a => R x a
    | inr b => S x b
    end;
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance HasProducts_Rel : HasProducts Rel :=
{
  product := Rel_product;
  outl    := Rel_outl;
  outr    := Rel_outr;
  fpair   := Rel_fpair;
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

Definition Rel_coproduct := Rel_product.

#[refine]
#[export]
Instance Rel_finl (X Y : Setoid') : RelHom X (Rel_coproduct X Y) :=
{
  rel := fun (x : X) (p : X + Y) =>
    match p with
    | inl x' => x == x'
    | _ => False
    end;
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance Rel_finr (X Y : Setoid') : RelHom Y (Rel_coproduct X Y) :=
{
  rel := fun (y : Y) (p : X + Y) =>
    match p with
    | inr y' => y == y'
    | _ => False
    end;
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance Rel_copair
  (A B X : Setoid') (R : RelHom A X) (S : RelHom B X)
  : RelHom (Rel_coproduct A B) X :=
{
  rel := fun (p : A + B) (x : X) =>
    match p with
    | inl a => R a x
    | inr b => S b x
    end;
}.
Proof. now rel. Defined.

#[refine]
#[export]
Instance HasCoproducts_Rel : HasCoproducts Rel :=
{
  coproduct := Rel_coproduct;
  finl      := Rel_finl;
  finr      := Rel_finr;
  copair    := Rel_copair;
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