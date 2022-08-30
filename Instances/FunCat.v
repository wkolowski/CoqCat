From Cat Require Import Cat.
From Cat.Universal Require Import Product Coproduct Exponential.

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
  intros. cbn. unfold ProductFunctor_fmap. now rewrite fpair_outl.
Defined.

#[refine]
#[export]
Instance FunCat_outr
  {C D : Cat} {hp : HasProducts D} {F G : Functor C D} : NatTrans (FunCat_product F G) G :=
{
  component := fun _ : Ob C => outr
}.
Proof.
  intros. cbn. unfold ProductFunctor_fmap. now rewrite fpair_outr.
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
  intros. cbn. unfold ProductFunctor_fmap. fpair; apply natural.
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
  split; cbn; intros; fpair.
  now apply fpair_equiv.
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
  intros. cbn. unfold CoproductFunctor_fmap. coprod.
Defined.

#[refine]
#[export]
Instance FunCat_finr
  {C D : Cat} {hp : HasCoproducts D} {F G : Functor C D} : NatTrans G (FunCat_coproduct F G) :=
{
  component := fun _ : Ob C => finr
}.
Proof.
  intros. cbn. unfold CoproductFunctor_fmap. coprod.
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
  destruct α, β; cbn in *. coprod.
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
  repeat split; cbn; intros; coprod.
  now apply copair_equiv.
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