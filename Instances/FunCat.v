From Cat Require Import Cat.
From Cat.Universal Require Import
  Initial Terminal Product Coproduct Equalizer Coequalizer Pullback Pushout Exponential.
From Cat.Universal Require Import Duality.

Set Implicit Arguments.

#[refine]
#[export]
Instance FunCat (C D : Cat) : Cat :=
{
  Ob := Functor C D;
  Hom := @NatTrans C D;
  HomSetoid := NatTransSetoid;
  comp := @NatTransComp C D;
  id := NatTransId
}.
Proof.
  (* Proper *) do 3 red; cbn; intros. now rewrite H, H0.
  (* Category laws *) all: cat.
Defined.

#[refine]
#[export]
Instance FunCat_init (C D : Cat) {hi : HasInit D} : Functor C D :=
{
  fob := fun _ => init D;
  fmap := fun _ _ _ => id (init D);
}.
Proof.
  all: easy.
Defined.

#[refine]
#[export]
Instance FunCat_create
  {C D : Cat} {hi : HasInit D} (F : Functor C D) : NatTrans (@FunCat_init C D hi) F :=
{
  component := fun X => create (fob F X);
}.
Proof.
  now intros; apply equiv_initial.
Defined.

#[refine]
#[export]
Instance HasInit_FunCat (C D : Cat) {hi : HasInit D} : HasInit (FunCat C D) :=
{
  init := @FunCat_init C D hi;
  create := @FunCat_create C D hi;
}.
Proof.
  red; cbn; intros F α β X.
  apply equiv_initial.
Defined.

#[export]
Instance HasStrictInit_FunCat
  (C D : Cat) {hi : HasInit D} {hsi : @HasStrictInit D hi}
  : HasStrictInit (FunCat C D).
Proof.
  intros F α; cbn in *.
  apply natural_isomorphism_char.
  intros X.
  apply hsi.
Defined.

#[refine]
#[export]
Instance FunCat_term (C D : Cat) {ht : HasTerm D} : Functor C D :=
{
  fob := fun _ => term D;
  fmap := fun _ _ _ => id (term D);
}.
Proof.
  all: easy.
Defined.

#[refine]
#[export]
Instance FunCat_delete
  {C D : Cat} {ht : HasTerm D} (F : Functor C D) : NatTrans F (@FunCat_term C D ht) :=
{
  component := fun X => delete (fob F X);
}.
Proof.
  now intros; apply equiv_terminal.
Defined.

#[refine]
#[export]
Instance HasTerm_FunCat (C D : Cat) {ht : HasTerm D} : HasTerm (FunCat C D) :=
{
  term := @FunCat_term C D ht;
  delete := @FunCat_delete C D ht;
}.
Proof.
  red; cbn; intros F α β X.
  apply equiv_terminal.
Defined.

#[export]
Instance HasStrictTerm_FunCat
  (C D : Cat) {ht : HasTerm D} {hst : @HasStrictTerm D ht}
  : HasStrictTerm (FunCat C D).
Proof.
  intros F α; cbn in *.
  apply natural_isomorphism_char.
  intros X.
  apply hst.
Defined.

#[refine]
#[export]
Instance FunCat_product {C D : Cat} {hp : HasProducts D} (F G : Functor C D) : Functor C D :=
{
  fob  := fun X : Ob C => product (fob F X) (fob G X);
  fmap := fun (X Y : Ob C) (f : Hom X Y) => fmap F f ×' fmap G f
}.
Proof.
  - proper.
  - now intros; rewrite !fmap_comp, bimap_comp.
  - now intros; rewrite !fmap_id, bimap_id.
Defined.

#[refine]
#[export]
Instance FunCat_outl
  {C D : Cat} {hp : HasProducts D} {F G : Functor C D} : NatTrans (FunCat_product F G) F :=
{
  component := fun _ : Ob C => outl
}.
Proof.
  now cbn; intros; rewrite fpair_outl.
Defined.

#[refine]
#[export]
Instance FunCat_outr
  {C D : Cat} {hp : HasProducts D} {F G : Functor C D} : NatTrans (FunCat_product F G) G :=
{
  component := fun _ : Ob C => outr
}.
Proof.
  now cbn; intros; rewrite fpair_outr.
Defined.

#[refine]
#[export]
Instance FunCat_fpair
  {C D : Cat} {hp : HasProducts D} {F G H : Functor C D}
  (α : NatTrans F G) (β : NatTrans F H) : NatTrans F (FunCat_product G H) :=
{
  component := fun X : Ob C => fpair (component α X) (component β X)
}.
Proof.
  now cbn; intros; solve_product; apply natural.
Defined.

#[refine]
#[export]
Instance HasProducts_FunCat {C D : Cat} {hp : HasProducts D} : HasProducts (FunCat C D) :=
{
  product := FunCat_product;
  outl := @FunCat_outl C D hp;
  outr := @FunCat_outr C D hp;
  fpair := fun (G H F : Functor C D) (α : @Hom (FunCat C D) F G) (β : @Hom (FunCat C D) F H) =>
    @FunCat_fpair C D hp F G H α β
}.
Proof.
  split; cbn; intros.
  - now apply fpair_outl.
  - now apply fpair_outr.
  - now apply equiv_product.
Defined.

#[refine]
#[export]
Instance FunCat_coproduct {C D : Cat} {hp : HasCoproducts D} (F G : Functor C D) : Functor C D :=
{
  fob := fun X : Ob C => coproduct (fob F X) (fob G X);
  fmap := fun (X Y : Ob C) (f : Hom X Y) => fmap F f +' fmap G f
}.
Proof.
  - now proper.
  - now intros; rewrite !fmap_comp, bimap_comp.
  - now intros; rewrite !fmap_id, bimap_id.
Defined.

#[refine]
#[export]
Instance FunCat_finl
  {C D : Cat} {hp : HasCoproducts D} {F G : Functor C D} : NatTrans F (FunCat_coproduct F G) :=
{
  component := fun _ : Ob C => finl
}.
Proof.
  now cbn; intros; rewrite finl_copair.
Defined.

#[refine]
#[export]
Instance FunCat_finr
  {C D : Cat} {hp : HasCoproducts D} {F G : Functor C D} : NatTrans G (FunCat_coproduct F G) :=
{
  component := fun _ : Ob C => finr
}.
Proof.
  now cbn; intros; rewrite finr_copair.
Defined.

#[refine]
#[export]
Instance FunCat_copair
  {C D : Cat} {hp : HasCoproducts D} {F G H : Functor C D}
  (α : NatTrans F H) (β : NatTrans G H) : NatTrans (FunCat_coproduct F G) H :=
{
  component := fun X : Ob C => copair (component α X) (component β X)
}.
Proof.
  now cbn; intros; solve_coproduct; apply natural.
Defined.

#[refine]
#[export]
Instance HasCoproducts_FunCat
  {C D : Cat} {hp : HasCoproducts D} : HasCoproducts (FunCat C D) :=
{
  coproduct := FunCat_coproduct;
  finl := @FunCat_finl C D hp;
  finr := @FunCat_finr C D hp;
  copair := fun (F G H : Functor C D)
    (α : @Hom (FunCat C D) F H) (β : @Hom (FunCat C D) G H)
    => @FunCat_copair C D hp F G H α β
}.
Proof.
  split; cbn; intros.
  - now apply finl_copair.
  - now apply finr_copair.
  - now apply equiv_coproduct.
Defined.

#[refine]
#[export]
Instance FunCat_equalizer
  {C D : Cat} {he : HasEqualizers D}
  {F G : Functor C D} (α β : NatTrans F G) : Functor C D :=
{
  fob := fun X : Ob C => equalizer (component α X) (component β X);
}.
Proof.
  - intros A B f.
    apply (factorize (equalize (component α A) (component β A) .> fmap F f)).
    abstract
    (
      rewrite !comp_assoc, <- !natural, <- !comp_assoc;
      f_equiv; apply Equalizer.ok
    ).
  - proper; apply equiv_equalizer.
    rewrite !factorize_equalize.
    now do 2 f_equiv.
  - cbn; intros; apply equiv_equalizer.
    rewrite factorize_equalize, comp_assoc, factorize_equalize,
      <- comp_assoc, factorize_equalize.
    now rewrite fmap_comp, comp_assoc.
  - cbn; intros; apply equiv_equalizer.
    now rewrite factorize_equalize, fmap_id, comp_id_l, comp_id_r.
Defined.

#[refine]
#[export]
Instance FunCat_equalize
  {C D : Cat} {he : HasEqualizers D}
  {F G : Functor C D} (α β : NatTrans F G) : NatTrans (FunCat_equalizer α β) F :=
{
  component := fun X => equalize (component α X) (component β X);
}.
Proof.
  now cbn; intros; rewrite factorize_equalize.
Defined.

#[refine]
#[export]
Instance FunCat_factorize
  {C D : Cat} {he : HasEqualizers D}
  {F G : Functor C D} (α β : NatTrans F G)
  (E : Functor C D) (γ : NatTrans E F) (Heq : NatTransComp γ α == NatTransComp γ β)
  : NatTrans E (FunCat_equalizer α β) :=
{
  component := fun X => factorize (component γ X) (Heq X);
}.
Proof.
  cbn; intros; apply equiv_equalizer.
  rewrite !comp_assoc, !factorize_equalize, <- comp_assoc, factorize_equalize.
  apply (natural γ).
Defined.

#[refine]
#[export]
Instance HasEqualizers_FunCat
  {C D : Cat} {he : HasEqualizers D} : HasEqualizers (FunCat C D) :=
{
  equalizer := @FunCat_equalizer C D he;
  equalize  := @FunCat_equalize C D he;
  factorize := @FunCat_factorize C D he;
}.
Proof.
  cbn; intros F G α β; split; cbn.
  - now intros X; apply Equalizer.ok.
  - now intros E γ Heq X; rewrite factorize_equalize.
  - intros E γ1 γ2 Heq X; apply equiv_equalizer, Heq.
Defined.

#[refine]
#[export]
Instance FunCat_coequalizer
  {C D : Cat} {he : HasCoequalizers D}
  {F G : Functor C D} (α β : NatTrans F G) : Functor C D :=
{
  fob := fun X : Ob C => coequalizer (component α X) (component β X);
}.
Proof.
  - intros A B f.
    apply (cofactorize (fmap G f .> coequalize (component α B) (component β B))).
    abstract
    (
      rewrite <- !comp_assoc, !natural, !comp_assoc;
      f_equiv; apply Coequalizer.ok
    ).
  - proper; apply equiv_coequalizer.
    rewrite !coequalize_cofactorize.
    now do 2 f_equiv.
  - cbn; intros; apply equiv_coequalizer.
    rewrite coequalize_cofactorize, <- comp_assoc, coequalize_cofactorize,
      comp_assoc, coequalize_cofactorize.
    now rewrite fmap_comp, comp_assoc.
  - cbn; intros; apply equiv_coequalizer.
    now rewrite coequalize_cofactorize, fmap_id, comp_id_l, comp_id_r.
Defined.

#[refine]
#[export]
Instance FunCat_coequalize
  {C D : Cat} {he : HasCoequalizers D}
  {F G : Functor C D} (α β : NatTrans F G) : NatTrans G (FunCat_coequalizer α β) :=
{
  component := fun X => coequalize (component α X) (component β X);
}.
Proof.
  now cbn; intros; rewrite coequalize_cofactorize.
Defined.

#[refine]
#[export]
Instance FunCat_cofactorize
  {C D : Cat} {he : HasCoequalizers D}
  {F G : Functor C D} (α β : NatTrans F G)
  (Q : Functor C D) (γ : NatTrans G Q) (Heq : NatTransComp α γ == NatTransComp β γ)
  : NatTrans (FunCat_coequalizer α β) Q :=
{
  component := fun X => cofactorize (component γ X) (Heq X);
}.
Proof.
  cbn; intros; apply equiv_coequalizer.
  rewrite <- !comp_assoc, !coequalize_cofactorize, comp_assoc, coequalize_cofactorize.
  apply (natural γ).
Defined.

#[refine]
#[export]
Instance HasCoequalizers_FunCat
  {C D : Cat} {he : HasCoequalizers D} : HasCoequalizers (FunCat C D) :=
{
  coequalizer := @FunCat_coequalizer C D he;
  coequalize  := @FunCat_coequalize C D he;
  cofactorize := @FunCat_cofactorize C D he;
}.
Proof.
  cbn; intros F G α β; split; cbn.
  - now intros X; apply Coequalizer.ok.
  - now intros E γ Heq X; rewrite coequalize_cofactorize.
  - intros E γ1 γ2 Heq X; apply equiv_coequalizer, Heq.
Defined.

#[refine]
#[export]
Instance FunCat_pullback
  {C D : Cat} {hp : HasPullbacks D}
  {F G H : Functor C D} (α : NatTrans F H) (β : NatTrans G H) : Functor C D :=
{
  fob := fun X : Ob C => pullback (component α X) (component β X);
}.
Proof.
  - intros A B f.
    apply (triple (pullL .> fmap F f) (pullR .> fmap G f)).
    abstract
    (
      rewrite !comp_assoc, <- !natural, <- !comp_assoc;
      f_equiv; apply Pullback.ok
    ).
  - proper; apply equiv_pullback.
    + now rewrite !triple_pullL, H0.
    + now rewrite !triple_pullR, H0.
  - cbn; intros; apply equiv_pullback; pullback_simpl.
    + now rewrite <- comp_assoc, triple_pullL, comp_assoc, fmap_comp.
    + now rewrite <- comp_assoc, triple_pullR, comp_assoc, fmap_comp.
  - cbn; intros; apply equiv_pullback.
    + now rewrite triple_pullL, fmap_id, comp_id_l, comp_id_r.
    + now rewrite triple_pullR, fmap_id, comp_id_l, comp_id_r.
Defined.

#[refine]
#[export]
Instance FunCat_pullL
  {C D : Cat} {hp : HasPullbacks D}
  {F G H : Functor C D} (α : NatTrans F H) (β : NatTrans G H)
  : NatTrans (FunCat_pullback α β) F :=
{
  component := fun _ : Ob C => pullL
}.
Proof.
  now cbn; intros; rewrite triple_pullL.
Defined.

#[refine]
#[export]
Instance FunCat_pullR
  {C D : Cat} {hp : HasPullbacks D}
  {F G H : Functor C D} (α : NatTrans F H) (β : NatTrans G H)
  : NatTrans (FunCat_pullback α β) G :=
{
  component := fun _ : Ob C => pullR
}.
Proof.
  now cbn; intros; rewrite triple_pullR.
Defined.

#[refine]
#[export]
Instance FunCat_triple
  {C D : Cat} {hp : HasPullbacks D}
  (F G H : Functor C D) (α : NatTrans F H) (β : NatTrans G H)
  {P : Functor C D} (x : NatTrans P F) (y : NatTrans P G)
  (Heq : NatTransComp x α == NatTransComp y β)
  : NatTrans P (FunCat_pullback α β) :=
{
  component := fun X : Ob C => triple (component x X) (component y X) (Heq X);
}.
Proof.
  cbn; intros; apply equiv_pullback.
  - rewrite !comp_assoc, !triple_pullL, <- comp_assoc, triple_pullL.
    now apply (natural x).
  - rewrite !comp_assoc, !triple_pullR, <- comp_assoc, triple_pullR.
    now apply (natural y).
Defined.

#[refine]
#[export]
Instance HasPullbacks_FunCat {C D : Cat} {hp : HasPullbacks D} : HasPullbacks (FunCat C D) :=
{
  pullback := @FunCat_pullback C D hp;
  pullL := @FunCat_pullL C D hp;
  pullR := @FunCat_pullR C D hp;
  triple := @FunCat_triple C D hp;
}.
Proof.
  split; cbn; intros.
  - now apply Pullback.ok.
  - now apply triple_pullL.
  - now apply triple_pullR.
  - now apply equiv_pullback.
Defined.

#[refine]
#[export]
Instance FunCat_exponential
  {C D : Cat} {hp : HasProducts D} {he : HasExponentials D}
  (F G : Functor C D) : Functor C D :=
{
  fob := fun X : Ob C => exponential (fob F X) (fob G X)
}.
Proof.
  - intros A B f.
    apply curry.
Abort.

(* TODO : transfer of exponentials. Do they even transfer? *)
#[refine]
#[export]
Instance HasExponentials_FunCat
  {C D : Cat} {hp : HasProducts D} {he : HasExponentials D}
  : HasExponentials (FunCat C D) := {}.
Proof.
Abort.