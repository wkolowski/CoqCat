From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Zero Product Coproduct Biproduct.
From Cat.Instances Require Import SETOID Mon CMon Grp.

Set Implicit Arguments.

Class AbGrp : Type :=
{
  grp :> Grp;
  op_comm : forall x y : grp, op x y == op y x;
}.

Coercion grp : AbGrp >-> Grp.

#[export]
Instance AbGrp2Mon (A : AbGrp) : CMon :=
{
  mon := A;
  op_comm := op_comm;
}.

Coercion AbGrp2Mon : AbGrp >-> CMon.

#[refine]
#[export]
Instance AbGrpCat : Cat :=
{
  Ob := AbGrp;
  Hom := MonHom;
  HomSetoid := MonHomSetoid;
  comp := MonComp;
  id := MonId;
}.
Proof.
  - intros A B C f1 f2 Hf g1 g2 Hg x; cbn in *.
    now rewrite Hf, Hg.
  - now cbn.
  - now cbn.
  - now cbn.
Defined.

#[refine]
#[export]
Instance AbGrp_zero : AbGrp :=
{
  grp := Grp_zero;
}.
Proof. all: easy. Defined.

#[refine]
#[export]
Instance HasInit_AbGrp : HasInit AbGrpCat :=
{
  init := AbGrp_zero;
  create := Mon_create;
}.
Proof.
  unfold isInitial; cbn; intros.
  now apply HasInit_Grp.
Defined.

#[refine]
#[export]
Instance HasTerm_AbGrp : HasTerm AbGrpCat :=
{
  term := AbGrp_zero;
  delete := Mon_delete;
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance HasZero_AbGrp : HasZero AbGrpCat :=
{
  HasInit_HasZero := HasInit_AbGrp;
  HasTerm_HasZero := HasTerm_AbGrp;
}.
Proof. now cbn. Defined.

#[refine]
#[export]
Instance AbGrp_product (X Y : AbGrp) : AbGrp :=
{
  grp := Grp_product X Y;
}.
Proof. now cbn; split; apply op_comm. Defined.

#[refine]
#[export]
Instance HasProducts_AbGrp : HasProducts AbGrpCat :=
{
  product := AbGrp_product;
  outl    := Mon_outl;
  outr    := Mon_outr;
  fpair   := Mon_fpair;
}.
Proof.
  split; cbn.
  - easy.
  - easy.
  - now split.
Defined.

Definition AbGrp_coproduct (A B : AbGrp) : AbGrp := AbGrp_product A B.

Definition AbGrp_finl {A B : AbGrp} : MonHom A (AbGrp_coproduct A B) :=
  @CMon_finl A B.

Definition AbGrp_finr {A B : AbGrp} : MonHom B (AbGrp_coproduct A B) :=
  @CMon_finr A B.

Definition AbGrp_copair
  {A B X : AbGrp} (f : MonHom A X) (g : MonHom B X) : MonHom (AbGrp_coproduct A B) X :=
    @CMon_copair A B X f g.

#[refine]
#[export]
Instance HasCoproducts_AbGrp : HasCoproducts AbGrpCat :=
{
  coproduct := @AbGrp_coproduct;
  finl      := @CMon_finl;
  finr      := @CMon_finr;
  copair    := @CMon_copair;
}.
Proof.
  split; cbn.
  - now intros; rewrite pres_neutr, neutr_r.
  - now intros; rewrite pres_neutr, neutr_l.
  - intros P' h1 h2 HA HB [a b]; cbn.
    assert (Heq' : @equiv _ (Mon_product A B) (a, b) (op a neutr, op neutr b))
      by now cbn; rewrite neutr_l, neutr_r.
    apply (Proper_func h1) in Heq'.
    assert (Heq :
        h1 (@op (CMon_coproduct A B) (a, neutr) (neutr, b))
          ==
        h2 (@op (CMon_coproduct A B) (a, neutr) (neutr, b)))
      by now rewrite !pres_op; f_equiv.
    rewrite Heq', Heq.
    apply (Proper_func h2); cbn.
    now rewrite neutr_l, neutr_r.
Defined.

#[refine]
#[export]
Instance HasBiproducts'_AbGrp : HasBiproducts' AbGrpCat :=
{
  biproduct := AbGrp_product;
  bioutl    := Mon_outl;
  bioutr    := Mon_outr;
  bipair    := Mon_fpair;
  binl      := @CMon_finl;
  binr      := @CMon_finr;
  bicopair  := @CMon_copair;
}.
Proof.
  - now apply HasProducts_AbGrp.
  - now apply HasCoproducts_AbGrp.
  - now cbn.
  - now cbn.
  - now cbn.
Defined.

#[refine]
#[export]
Instance AbGrp_equalizer {A B : AbGrp} (f g : MonHom A B) : AbGrp :=
{
  grp := Grp_equalizer f g;
}.
Proof.
  intros [x Hx] [y Hy]; cbn.
  now apply op_comm.
Defined.

#[refine]
#[export]
Instance HasEqualizers_AbGrp : HasEqualizers AbGrpCat :=
{
  equalizer := @AbGrp_equalizer;
  equalize  := @Mon_equalize;
  factorize := @Mon_factorize;
}.
Proof.
  split; cbn.
  - now intros [x H]; cbn.
  - easy.
  - easy.
Defined.

#[refine]
#[export]
Instance AbGrp_coequalizer {A B : AbGrp} (f g : MonHom A B) : AbGrp :=
{
  grp := Grp_coequalizer f g;
}.
Proof.
  now cbn; intros; apply SgrCE_refl, op_comm.
Defined.

#[refine]
#[export]
Instance HasCoequalizers_AbGrp : HasCoequalizers AbGrpCat :=
{
  coequalizer := @AbGrp_coequalizer;
  coequalize  := @Mon_coequalize;
  cofactorize := @Mon_cofactorize;
}.
Proof.
  split; cbn.
  - now constructor.
  - easy.
  - easy.
Defined.

#[refine]
#[export]
Instance AbGrp_pullback
  {A B X : AbGrp} (f : MonHom A X) (g : MonHom B X) : AbGrp :=
{
  grp := Grp_pullback f g;
}.
Proof.
  intros [a1 b1 ok1] [a2 b2 ok2]; cbn.
  now split; apply op_comm.
Defined.

#[refine]
#[export]
Instance HasPullbacks_AbGrp : HasPullbacks AbGrpCat :=
{
  pullback := @AbGrp_pullback;
  pullL    := @Mon_pullL;
  pullR    := @Mon_pullR;
  triple   := @Mon_triple;
}.
Proof.
  split; cbn.
  - now apply ok.
  - easy.
  - easy.
  - now split.
Defined.

(* We construct pushouts from coproducts and coequalizers. *)
#[export] Instance HasPushouts_AbGrp : HasPushouts AbGrpCat :=
  HasPushouts_HasCoproducts_HasCoequalizers HasCoproducts_AbGrp HasCoequalizers_AbGrp.