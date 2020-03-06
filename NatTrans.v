Require Import Cat.Base.

Require Import Cat.Functor.
Require Import BinProdCoprod.
Require Import Exponential.

Set Implicit Arguments.

Class NatTrans {C D : Cat} (T S : Functor C D) : Type :=
{
    component : forall X : Ob C, Hom (fob T X) (fob S X);
    coherence : forall (X Y : Ob C) (f : Hom X Y),
      component X .> fmap S f == fmap T f .> component Y
}.

Arguments component [C D T S] _ _.
Arguments coherence [C D T S] _ [X Y] _.

#[refine]
Instance NatTransSetoid {C D : Cat} (F G : Functor C D)
    : Setoid (NatTrans F G) :=
{
    equiv := fun alfa beta : NatTrans F G =>
      forall X : Ob C, component alfa X == component beta X
}.
Proof.
  split; red; intros; try rewrite H; try rewrite H0; reflexivity.
Defined.

#[refine]
Instance NatTransComp {C D : Cat}
    {F : Functor C D} {G : Functor C D} {H : Functor C D}
    (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H :=
{
    component := fun X : Ob C => component α X .> component β X
}.
Proof.
  intros. destruct α, β; simpl in *.
  rewrite !comp_assoc, coherence1, <- comp_assoc, coherence0. cat.
Defined.

#[refine]
Instance NatTransId {C D : Cat} (F : Functor C D) : NatTrans F F :=
{
    component := fun X : Ob C => id (fob F X)
}.
Proof. cat. Defined.

#[refine]
Instance FunCat (C D : Cat) : Cat :=
{
    Ob := Functor C D;
    Hom := @NatTrans C D;
    HomSetoid := NatTransSetoid;
    comp := @NatTransComp C D;
    id := NatTransId
}.
Proof.
  (* Proper *) do 3 red; simpl; intros. rewrite H, H0. reflexivity.
  (* Category laws *) all: cat.
Defined.

Definition natural_isomorphism {C D : Cat} {F G : Functor C D}
    (α : NatTrans F G) : Prop := exists β : NatTrans G F,
    NatTransComp α β == NatTransId F /\
    NatTransComp β α == NatTransId G.

Theorem natural_isomorphism_char :
    forall (C D : Cat) (F G : Functor C D) (α : NatTrans F G),
    natural_isomorphism α <-> forall X : Ob C, Iso (component α X).
Proof.
  unfold natural_isomorphism; split; simpl; intros.
    destruct H as [β [Η1 Η2]]. red. exists (component β X). auto.
    red in H. destruct α as [component_α coherence_α]; simpl in *.
    assert (component_β : {f : forall X : Ob C, Hom (fob G X) (fob F X) |
    (forall X : Ob C, component_α X .> f X == id (fob F X) /\
      f X .> component_α X == id (fob G X)) /\
    (forall (X Y : Ob C) (g : Hom X Y), f X .> fmap F g == fmap G g .> f Y)}).
      pose (H' := fun X : Ob C => constructive_indefinite_description _ (H X)).
      exists (fun X : Ob C => proj1_sig (H' X)). split.
        intros. split; destruct (H' X); cat.
        intros. destruct (H' X), (H' Y). simpl in *. cat. clear H'.
        assert (
        x .> component_α X .> x .> fmap F g .> component_α Y .> x0 ==
        x .> component_α X .> fmap G g .> x0 .> component_α Y .> x0). cat.
          rewrite <- (comp_assoc (component_α X) x).
          rewrite <- (comp_assoc x0 (component_α Y)).
          rewrite <- (comp_assoc (fmap F g) _).
          rewrite <- (comp_assoc _ (fmap G g)).
          rewrite H2, H1, coherence_α. cat.
        rewrite H3 in H4. rewrite !comp_assoc in H4.
        rewrite H0 in H4. cat.
    destruct component_β as [component_β [inverse_α_β coherence_β]].
    eexists {| component := component_β; coherence := coherence_β |}.
    cat; apply inverse_α_β.
Defined.

#[refine]
Instance FunCat_prodOb {C D : Cat} {hp : has_products D}
    (F G : Functor C D) : Functor C D :=
{
    fob := fun X : Ob C => prodOb (fob F X) (fob G X);
    fmap := fun (X Y : Ob C) (f : Hom X Y) =>
      ProductFunctor_fmap (fmap F f) (fmap G f)
}.
Proof.
  proper.
  intros. rewrite 2 pres_comp, ProductFunctor_fmap_pres_comp. reflexivity.
  intros. rewrite 2 pres_id, ProductFunctor_fmap_pres_id. reflexivity.
Defined.

#[refine]
Instance FunCat_proj1 {C D : Cat} {hp : has_products D}
    {F G : Functor C D} : NatTrans (FunCat_prodOb F G) F :=
{
    component := fun _ : Ob C => proj1
}.
Proof.
  intros. cbn. unfold ProductFunctor_fmap. fpair.
Defined.

#[refine]
Instance FunCat_proj2 {C D : Cat} {hp : has_products D}
    {F G : Functor C D} : NatTrans (FunCat_prodOb F G) G :=
{
    component := fun _ : Ob C => proj2
}.
Proof.
  intros. cbn. unfold ProductFunctor_fmap. fpair.
Defined.

#[refine]
Instance FunCat_fpair
    {C D : Cat} {hp : has_products D} {F G H : Functor C D}
    (α : NatTrans F G) (β : NatTrans F H) : NatTrans F (FunCat_prodOb G H) :=
{
    component := fun X : Ob C => fpair (component α X) (component β X)
}.
Proof.
  intros. simpl. unfold ProductFunctor_fmap.
  destruct α, β; simpl in *. fpair.
Defined.

#[refine]
Instance FunCat_has_products {C D : Cat} {hp : has_products D}
    : has_products (FunCat C D) :=
{
    prodOb := FunCat_prodOb;
    proj1 := @FunCat_proj1 C D hp;
    proj2 := @FunCat_proj2 C D hp;
    fpair := fun (G H F : Functor C D)
      (α : @Hom (FunCat C D) F G) (β : @Hom (FunCat C D) F H)
      => @FunCat_fpair C D hp F G H α β
}.
Proof.
  proper. fpair.
  repeat split; simpl; intros; fpair.
  destruct H. rewrite H, H0. fpair.
Defined.

#[refine]
Instance FunCat_coprodOb {C D : Cat} {hp : has_coproducts D}
    (F G : Functor C D) : Functor C D :=
{
    fob := fun X : Ob C => coprodOb (fob F X) (fob G X);
    fmap := fun (X Y : Ob C) (f : Hom X Y) =>
      CoproductFunctor_fmap (fmap F f) (fmap G f)
}.
Proof.
  proper.
  intros. rewrite 2 pres_comp, CoproductFunctor_fmap_pres_comp. reflexivity.
  intros. rewrite 2 pres_id, CoproductFunctor_fmap_pres_id. reflexivity.
Defined.

#[refine]
Instance FunCat_coproj1 {C D : Cat} {hp : has_coproducts D}
    {F G : Functor C D} : NatTrans F (FunCat_coprodOb F G) :=
{
    component := fun _ : Ob C => coproj1
}.
Proof.
  intros. simpl. unfold CoproductFunctor_fmap. copair.
Defined.

#[refine]
Instance FunCat_coproj2 {C D : Cat} {hp : has_coproducts D}
    {F G : Functor C D} : NatTrans G (FunCat_coprodOb F G) :=
{
    component := fun _ : Ob C => coproj2
}.
Proof.
  intros. simpl. unfold CoproductFunctor_fmap. copair.
Defined.

#[refine]
Instance FunCat_copair
    {C D : Cat} {hp : has_coproducts D} {F G H : Functor C D}
    (α : NatTrans F H) (β : NatTrans G H) : NatTrans (FunCat_coprodOb F G) H :=
{
    component := fun X : Ob C => copair (component α X) (component β X)
}.
Proof.
  intros. simpl. unfold CoproductFunctor_fmap.
  destruct α, β; simpl in *. copair.
Defined.

#[refine]
Instance FunCat_has_coproducts {C D : Cat} {hp : has_coproducts D}
  : has_coproducts (FunCat C D) :=
{
    coprodOb := FunCat_coprodOb;
    coproj1 := @FunCat_coproj1 C D hp;
    coproj2 := @FunCat_coproj2 C D hp;
    copair := fun (F G H : Functor C D)
      (α : @Hom (FunCat C D) F H) (β : @Hom (FunCat C D) G H)
      => @FunCat_copair C D hp F G H α β
}.
Proof.
  proper. copair.
  repeat split; simpl; intros; copair.
  destruct H. rewrite H, H0. copair.
Defined.

(* TODO *)
#[refine]
Instance FunCat_expOb
  {C D : Cat} {hp : has_products D} {he : has_exponentials D}
  (F G : Functor C D) : Functor C D :=
{
    fob := fun X : Ob C => expOb (fob F X) (fob G X)
}.
Proof.
  intros.
  Focus 2. unfold Proper, respectful. intros. proper.
Abort.

(* TODO : transfer of exponentials. Do they even transfer? *)
#[refine]
Instance FunCat_has_exponentials
  {C D : Cat} {hp : has_products D} {he : has_exponentials D}
  : has_exponentials (FunCat C D) :=
{}.
Proof.
Abort.