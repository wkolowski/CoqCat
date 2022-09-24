From CoqAlgs.Sorting Require Import Perm InsertionSort.

From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Zero Product Coproduct.
From Cat Require Export Instances.Setoid.Mon.

Set Implicit Arguments.

Class CMon : Type :=
{
  mon :> Mon;
  op_comm: forall x y : mon, op x y == op y x
}.

Arguments mon _ : clear implicits.

Coercion mon : CMon >-> Mon.

#[export]
Instance CMonCat : Cat :=
{
  Ob := CMon;
  Hom := MonHom;
  HomSetoid := MonHomSetoid;
  comp := MonComp;
  id := MonId;
  Proper_comp := @Proper_comp MonCat;
  comp_id_l := @comp_id_l MonCat;
  comp_id_r := @comp_id_r MonCat;
  comp_assoc := @comp_assoc MonCat;
}.

#[refine]
#[export]
Instance CMon_init : CMon :=
{
  mon := Mon_init;
}.
Proof. easy. Defined.

#[export]
Instance HasInit_CMon : HasInit CMonCat :=
{
  init := CMon_init;
  create := Mon_create;
  isInitial_HasInit' := @isInitial_HasInit' MonCat _;
}.

#[refine]
#[export]
Instance CMon_term : CMon :=
{
  mon := Mon_term;
}.
Proof. easy. Defined.

#[export]
Instance HasTerm_CMon : HasTerm CMonCat :=
{
  term := CMon_term;
  delete := Mon_delete;
  isTerminal_HasTerm' := @isTerminal_HasTerm' MonCat _;
}.

#[refine]
#[export]
Instance HasZero_CMon : HasZero CMonCat :=
{
  HasInit_HasZero := HasInit_CMon;
  HasTerm_HasZero := HasTerm_CMon
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance CMon_product (A B : CMon) : CMon :=
{
  mon := Mon_product A B;
}.
Proof.
  intros [a1 b1] [a2 b2]; cbn.
  now split; apply op_comm.
Defined.

#[refine]
#[export]
Instance HasProducts_CMon : HasProducts CMonCat :=
{
  product := CMon_product;
  outl := Mon_outl;
  outr := Mon_outr;
  fpair := Mon_fpair;
}.
Proof.
  now repeat split; cbn in *.
Defined.

#[export]
Instance CMon_coproduct (A B : CMon) : CMon := CMon_product A B.

Definition CMon_finl' (A B : CMon) : SetoidHom A (CMon_coproduct A B).
Proof.
  esplit. Unshelve. all: cycle 1.
  - exact (fun a => (a, neutr)).
  - now intros x y Heq; cbn.
Defined.

Definition CMon_finl (A B : CMon) : MonHom A (CMon_coproduct A B).
Proof.
  esplit. Unshelve. all: cycle 1.
  - esplit with (CMon_finl' A B); cbn.
    now intros; rewrite neutr_l.
  - easy.
Defined.

Definition CMon_finr' (A B : CMon) : SetoidHom B (CMon_coproduct A B).
Proof.
  esplit. Unshelve. all: cycle 1.
  - exact (fun b => (neutr, b)).
  - now intros x y Heq; cbn.
Defined.

Definition CMon_finr (A B : CMon) : MonHom B (CMon_coproduct A B).
Proof.
  esplit. Unshelve. all: cycle 1.
  - esplit with (CMon_finr' A B); cbn.
    now intros; rewrite neutr_l.
  - easy.
Defined.

#[export]
Instance CMon_copair'
  {A B X : CMon} (f : MonHom A X) (g : MonHom B X) : SetoidHom (CMon_coproduct A B) X.
Proof.
  esplit. Unshelve. all: cycle 1.
  - refine (fun '(a, b) => op (f a) (g b)).
  - now intros [a1 b1] [a2 b2]; cbn; intros [-> ->].
Defined.

#[export]
Instance CMon_copair
  {A B X : CMon} (f : MonHom A X) (g : MonHom B X) : MonHom (CMon_coproduct A B) X.
Proof.
  esplit. Unshelve. all: cycle 1.
  - esplit with (CMon_copair' f g); cbn.
    intros [a1 b1] [a2 b2]; cbn.
    rewrite !pres_op.
    rewrite !assoc; f_equiv.
    rewrite <- !assoc; f_equiv.
    apply op_comm.
  - now cbn; rewrite !pres_neutr, neutr_l.
Defined.

#[refine]
#[export]
Instance HasCoproducts_CMon : HasCoproducts CMonCat :=
{
  coproduct := CMon_coproduct;
  finl := CMon_finl;
  finr := CMon_finr;
  copair := @CMon_copair;
}.
Proof.
  split; cbn.
  - now intros; rewrite pres_neutr, neutr_r.
  - now intros; rewrite pres_neutr, neutr_l.
  - intros P' h1 h2 HA HB [a b]; cbn.
    assert (Heq :
        h1 (@op (CMon_coproduct A B) (a, neutr) (neutr, b))
          ==
        h2 (@op (CMon_coproduct A B) (a, neutr) (neutr, b)))
      by now rewrite !pres_op; f_equiv.
    assert (Heq' : @equiv _ (Mon_product A B) (a, b) (op a neutr, op neutr b))
      by now cbn; rewrite neutr_l, neutr_r.
    rewrite Heq'. rewrite (@pres_op _ _ h1 (op a neutr) (op neutr b)).
Admitted.

#[refine]
#[export]
Instance forgetful : Functor CMonCat MonCat :=
{
  fob := mon;
}.
Proof.
  - easy.
  - easy.
Defined.