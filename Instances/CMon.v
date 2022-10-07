From CoqAlgs.Sorting Require Import Perm InsertionSort.

From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Zero Product Coproduct.
From Cat Require Export Instances.Mon.

Set Implicit Arguments.

Class CMon : Type :=
{
  mon :> Mon;
  op_comm : forall x y : mon, op x y == op y x;
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
Instance forgetful : Functor CMonCat MonCat :=
{
  fob := mon;
}.
Proof.
  - easy.
  - easy.
Defined.

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
  split with (fun a => (a, neutr)).
  now intros x y Heq; cbn.
Defined.

Definition CMon_finl {A B : CMon} : MonHom A (CMon_coproduct A B).
Proof.
  unshelve esplit.
  - split with (CMon_finl' A B); cbn.
    now split; [| symmetry; apply neutr_r].
  - now cbn.
Defined.

Definition CMon_finr' (A B : CMon) : SetoidHom B (CMon_coproduct A B).
Proof.
  split with (fun b => (neutr, b)).
  now intros x y Heq; cbn.
Defined.

Definition CMon_finr {A B : CMon} : MonHom B (CMon_coproduct A B).
Proof.
  unshelve esplit.
  - split with (CMon_finr' A B); cbn.
    now split; [symmetry; apply neutr_l |].
  - now cbn.
Defined.

#[export]
Instance CMon_copair'
  {A B X : CMon} (f : MonHom A X) (g : MonHom B X) : SetoidHom (CMon_coproduct A B) X.
Proof.
  unshelve esplit.
  - now refine (fun x => op (f (fst x)) (g (snd x))).
  - now intros a b [Ha Hb]; f_equiv; apply Proper_func.
Defined.

#[export]
Instance CMon_copair
  {A B X : CMon} (f : MonHom A X) (g : MonHom B X) : MonHom (CMon_coproduct A B) X.
Proof.
  unshelve esplit.
  - split with (CMon_copair' f g); cbn.
    intros [a1 b1] [a2 b2]; cbn.
    rewrite !pres_op.
    rewrite !assoc; f_equiv.
    rewrite <- !assoc; f_equiv.
    now apply op_comm.
  - now cbn; rewrite !pres_neutr, neutr_l.
Defined.

#[refine]
#[export]
Instance HasCoproducts_CMon : HasCoproducts CMonCat :=
{
  coproduct := CMon_coproduct;
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
Instance CMon_equalizer {A B : CMon} (f g : MonHom A B) : CMon :=
{
  mon := Mon_equalizer f g;
}.
Proof.
  intros [x Hx] [y Hy]; cbn.
  now apply op_comm.
Defined.

#[refine]
#[export]
Instance CMon_equalize {A B : CMon} (f g : MonHom A B) : MonHom (CMon_equalizer f g) A :=
{
  sgrHom := Sgr_equalize f g;
}.
Proof.
  now cbn.
Defined.

#[refine]
#[export]
Instance CMon_factorize
  {A B : CMon} {f g : MonHom A B}
  {E' : CMon} (e' : Hom E' A) (Heq : (e' .> f) == (e' .> g))
  : MonHom E' (CMon_equalizer f g) :=
{
  sgrHom := Sgr_factorize Heq;
}.
Proof.
  now cbn; rewrite pres_neutr.
Defined.

#[refine]
#[export]
Instance HasEqualizers_CMon : HasEqualizers CMonCat :=
{
  equalizer := @CMon_equalizer;
  equalize  := @CMon_equalize;
  factorize := @CMon_factorize;
}.
Proof.
  split; cbn.
  - now intros [x H]; cbn.
  - easy.
  - easy.
Defined.

#[refine]
#[export]
Instance CMon_coequalizer {A B : CMon} (f g : MonHom A B) : CMon :=
{
  mon := Mon_coequalizer f g;
}.
Proof.
  now cbn; intros; apply SgrCE_refl, op_comm.
Defined.

#[refine]
#[export]
Instance CMon_coequalize {A B : CMon} {f g : MonHom A B} : MonHom B (CMon_coequalizer f g) :=
{
  sgrHom := @Sgr_coequalize A B f g;
}.
Proof.
  now cbn.
Defined.

#[export]
#[refine]
Instance CMon_cofactorize
  {A B : CMon} {f g : Hom A B}
  {Q : CMon} (q : Hom B Q) (Heq : f .> q == g .> q)
  : MonHom (CMon_coequalizer f g) Q :=
{
  sgrHom := Sgr_cofactorize Heq;
}.
Proof.
  now cbn; apply pres_neutr.
Defined.

#[refine]
#[export]
Instance HasCoequalizers_CMon : HasCoequalizers CMonCat :=
{
  coequalizer := @CMon_coequalizer;
  coequalize  := @CMon_coequalize;
  cofactorize := @CMon_cofactorize;
}.
Proof.
  split; cbn.
  - now constructor.
  - easy.
  - easy.
Defined.

#[refine]
#[export]
Instance CMon_pullback
  {A B X : CMon} (f : MonHom A X) (g : MonHom B X) : CMon :=
{
  mon := Mon_pullback f g;
}.
Proof.
  - intros [a1 b1 H1] [a2 b2 H2]; cbn.
    now split; apply op_comm.
Defined.

#[refine]
#[export]
Instance CMon_pullL
  {A B X : CMon} (f : MonHom A X) (g : MonHom B X) : MonHom (CMon_pullback f g) A :=
{
  sgrHom := Mon_pullL f g;
}.
Proof.
  now cbn.
Defined.

#[refine]
#[export]
Instance CMon_pullR
  {A B X : CMon} (f : MonHom A X) (g : MonHom B X) : MonHom (CMon_pullback f g) B :=
{
  sgrHom := Mon_pullR f g;
}.
Proof.
  now cbn.
Defined.

#[refine]
#[export]
Instance CMon_triple
  {A B X : CMon} (f : Hom A X) (g : Hom B X)
  {Γ : CMon} (a : Hom Γ A) (b : Hom Γ B) (Heq : a .> f == b .> g)
  : MonHom Γ (CMon_pullback f g) :=
{
  sgrHom := Mon_triple Heq;
}.
Proof.
  now cbn; rewrite !pres_neutr.
Defined.

#[refine]
#[export]
Instance HasPullbacks_CMon : HasPullbacks CMonCat :=
{
  pullback := @CMon_pullback;
  pullL    := @CMon_pullL;
  pullR    := @CMon_pullR;
  triple   := @CMon_triple;
}.
Proof.
  split; cbn.
  - now apply ok.
  - easy.
  - easy.
  - now split.
Defined.

(* We construct pushouts from coproducts and coequalizers. *)
#[export] Instance HasPushouts_CMon : HasPushouts CMonCat :=
  HasPushouts_HasCoproducts_HasCoequalizers HasCoproducts_CMon HasCoequalizers_CMon.