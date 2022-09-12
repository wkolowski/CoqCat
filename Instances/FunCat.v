From Cat Require Import Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct Equalizer Coequalizer Exponential.

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

#[refine]
#[export]
Instance FunCat_product {C D : Cat} {hp : HasProducts D} (F G : Functor C D) : Functor C D :=
{
  fob := fun X : Ob C => product (fob F X) (fob G X);
  fmap := fun (X Y : Ob C) (f : Hom X Y) => ProductFunctor_fmap (fmap F f) (fmap G f)
}.
Proof.
  proper.
  now intros; rewrite 2 fmap_comp, ProductFunctor_fmap_comp.
  now intros; rewrite 2 fmap_id, ProductFunctor_fmap_id.
Defined.

#[refine]
#[export]
Instance FunCat_outl
  {C D : Cat} {hp : HasProducts D} {F G : Functor C D} : NatTrans (FunCat_product F G) F :=
{
  component := fun _ : Ob C => outl
}.
Proof.
  cbn; unfold ProductFunctor_fmap; intros.
  now rewrite fpair_outl.
Defined.

#[refine]
#[export]
Instance FunCat_outr
  {C D : Cat} {hp : HasProducts D} {F G : Functor C D} : NatTrans (FunCat_product F G) G :=
{
  component := fun _ : Ob C => outr
}.
Proof.
  cbn; unfold ProductFunctor_fmap; intros.
  now rewrite fpair_outr.
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
  cbn; unfold ProductFunctor_fmap; intros.
  solve_product; apply natural.
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
  split; cbn; intros; solve_product.
  now apply equiv_product.
Defined.

#[refine]
#[export]
Instance FunCat_coproduct {C D : Cat} {hp : HasCoproducts D} (F G : Functor C D) : Functor C D :=
{
  fob := fun X : Ob C => coproduct (fob F X) (fob G X);
  fmap := fun (X Y : Ob C) (f : Hom X Y) =>
    CoproductFunctor_fmap (fmap F f) (fmap G f)
}.
Proof.
  - proper.
  - now intros; rewrite 2 fmap_comp, CoproductFunctor_fmap_comp.
  - now intros; rewrite 2 fmap_id, CoproductFunctor_fmap_id.
Defined.

#[refine]
#[export]
Instance FunCat_finl
  {C D : Cat} {hp : HasCoproducts D} {F G : Functor C D} : NatTrans F (FunCat_coproduct F G) :=
{
  component := fun _ : Ob C => finl
}.
Proof.
  intros. cbn. unfold CoproductFunctor_fmap. solve_coproduct.
Defined.

#[refine]
#[export]
Instance FunCat_finr
  {C D : Cat} {hp : HasCoproducts D} {F G : Functor C D} : NatTrans G (FunCat_coproduct F G) :=
{
  component := fun _ : Ob C => finr
}.
Proof.
  intros. cbn. unfold CoproductFunctor_fmap. solve_coproduct.
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
  intros. cbn. unfold CoproductFunctor_fmap.
  destruct α, β; cbn in *. solve_coproduct.
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
  repeat split; cbn; intros; solve_coproduct.
  now apply equiv_coproduct.
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
      f_equiv; apply equalize_ok
    ).
  - proper; apply equiv_equalizer.
    rewrite !factorize_equalize.
    now do 2 f_equiv.
  - cbn; intros; apply equiv_equalizer.
    rewrite factorize_equalize, comp_assoc, factorize_equalize, <- comp_assoc, factorize_equalize.
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
  - now intros X; apply equalize_ok.
  - now intros E γ Heq X; rewrite factorize_equalize.
  - intros E γ1 γ2 Heq X; apply equiv_equalizer, Heq.
Defined.

#[refine]
#[export]
Instance FunCat_expOb
  {C D : Cat} {hp : HasProducts D} {he : HasExponentials D}
  (F G : Functor C D) : Functor C D :=
{
  fob := fun X : Ob C => expOb (fob F X) (fob G X)
}.
Proof.
Abort.

(* TODO : transfer of exponentials. Do they even transfer? *)
#[refine]
#[export]
Instance HasExponentials_FunCat
  {C D : Cat} {hp : HasProducts D} {he : HasExponentials D}
  : HasExponentials (FunCat C D) := {}.
Proof.
Abort.