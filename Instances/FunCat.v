From Cat Require Import Cat.
From Cat.Limits Require Import Product Coproduct Exponential.

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
  (* Proper *) do 3 red; cbn; intros. rewrite H, H0. reflexivity.
  (* Category laws *) all: cat.
Defined.

#[refine]
#[export]
Instance FunCat_prodOb {C D : Cat} {hp : HasProducts D} (F G : Functor C D) : Functor C D :=
{
  fob := fun X : Ob C => prodOb (fob F X) (fob G X);
  fmap := fun (X Y : Ob C) (f : Hom X Y) => ProductFunctor_fmap (fmap F f) (fmap G f)
}.
Proof.
  proper.
  intros. rewrite 2 fmap_comp, ProductFunctor_fmap_comp. reflexivity.
  intros. rewrite 2 fmap_id, ProductFunctor_fmap_id. reflexivity.
Defined.

#[refine]
#[export]
Instance FunCat_outl
  {C D : Cat} {hp : HasProducts D} {F G : Functor C D} : NatTrans (FunCat_prodOb F G) F :=
{
  component := fun _ : Ob C => outl
}.
Proof.
  intros. cbn. unfold ProductFunctor_fmap. fpair.
Defined.

#[refine]
#[export]
Instance FunCat_outr
  {C D : Cat} {hp : HasProducts D} {F G : Functor C D} : NatTrans (FunCat_prodOb F G) G :=
{
  component := fun _ : Ob C => outr
}.
Proof.
  intros. cbn. unfold ProductFunctor_fmap. fpair.
Defined.

#[refine]
#[export]
Instance FunCat_fpair
  {C D : Cat} {hp : HasProducts D} {F G H : Functor C D}
  (α : NatTrans F G) (β : NatTrans F H) : NatTrans F (FunCat_prodOb G H) :=
{
  component := fun X : Ob C => fpair (component α X) (component β X)
}.
Proof.
  intros. cbn. unfold ProductFunctor_fmap.
  destruct α, β; cbn in *. fpair.
Defined.

#[refine]
#[export]
Instance HasProducts_FunCat {C D : Cat} {hp : HasProducts D} : HasProducts (FunCat C D) :=
{
  prodOb := FunCat_prodOb;
  outl := @FunCat_outl C D hp;
  outr := @FunCat_outr C D hp;
  fpair := fun (G H F : Functor C D) (α : @Hom (FunCat C D) F G) (β : @Hom (FunCat C D) F H) =>
    @FunCat_fpair C D hp F G H α β
}.
Proof.
  proper. fpair.
  repeat split; cbn; intros; fpair.
  destruct H. rewrite H, H0. fpair.
Defined.

#[refine]
#[export]
Instance FunCat_coprodOb {C D : Cat} {hp : HasCoproducts D} (F G : Functor C D) : Functor C D :=
{
  fob := fun X : Ob C => coprodOb (fob F X) (fob G X);
  fmap := fun (X Y : Ob C) (f : Hom X Y) =>
    CoproductFunctor_fmap (fmap F f) (fmap G f)
}.
Proof.
  proper.
  intros. rewrite 2 fmap_comp, CoproductFunctor_fmap_comp. reflexivity.
  intros. rewrite 2 fmap_id, CoproductFunctor_fmap_id. reflexivity.
Defined.

#[refine]
#[export]
Instance FunCat_finl
  {C D : Cat} {hp : HasCoproducts D} {F G : Functor C D} : NatTrans F (FunCat_coprodOb F G) :=
{
  component := fun _ : Ob C => finl
}.
Proof.
  intros. cbn. unfold CoproductFunctor_fmap. copair.
Defined.

#[refine]
#[export]
Instance FunCat_finr
  {C D : Cat} {hp : HasCoproducts D} {F G : Functor C D} : NatTrans G (FunCat_coprodOb F G) :=
{
  component := fun _ : Ob C => finr
}.
Proof.
  intros. cbn. unfold CoproductFunctor_fmap. copair.
Defined.

#[refine]
#[export]
Instance FunCat_copair
  {C D : Cat} {hp : HasCoproducts D} {F G H : Functor C D}
  (α : NatTrans F H) (β : NatTrans G H) : NatTrans (FunCat_coprodOb F G) H :=
{
  component := fun X : Ob C => copair (component α X) (component β X)
}.
Proof.
  intros. cbn. unfold CoproductFunctor_fmap.
  destruct α, β; cbn in *. copair.
Defined.

#[refine]
#[export]
Instance HasCoproducts_FunCat
  {C D : Cat} {hp : HasCoproducts D} : HasCoproducts (FunCat C D) :=
{
  coprodOb := FunCat_coprodOb;
  finl := @FunCat_finl C D hp;
  finr := @FunCat_finr C D hp;
  copair := fun (F G H : Functor C D)
    (α : @Hom (FunCat C D) F H) (β : @Hom (FunCat C D) G H)
    => @FunCat_copair C D hp F G H α β
}.
Proof.
  proper. copair.
  repeat split; cbn; intros; copair.
  destruct H. rewrite H, H0. copair.
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