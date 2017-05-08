Add Rec LoadPath "/home/zeimer/Code/Coq".

(*Require Import Coq.Logic.IndefiniteDescription.*)
Require Import Cat.Base.

Require Import Functor.
Require Import BinProdCoprod.

Class NatTrans {C D : Cat} (T S : Functor C D) : Type :=
{
    component : forall X : Ob C, Hom (fob T X) (fob S X);
    coherence : forall (X Y : Ob C) (f : Hom X Y),
      component X .> fmap S f == fmap T f .> component Y
}.

Arguments component [C] [D] [T] [S] _ _.

Instance NatTransSetoid {C D : Cat} (F G : Functor C D)
    : Setoid (NatTrans F G) :=
{
    equiv := fun alfa beta : NatTrans F G =>
      forall X : Ob C, component alfa X == component beta X
}.
Proof.
  split; red; intros; try rewrite H; try rewrite H0; reflexivity.
Defined.

Instance NatTransComp {C D : Cat}
    {F : Functor C D} {G : Functor C D} {H : Functor C D}
    (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H :=
{
    component := fun X : Ob C => component α X .> component β X
}.
Proof.
  intros. destruct α, β; simpl in *. repeat rewrite comp_assoc.
  rewrite coherence1. rewrite <- comp_assoc. rewrite coherence0. cat.
Defined.

Instance NatTransId {C D : Cat} (F : Functor C D) : NatTrans F F :=
{
    component := fun X : Ob C => id (fob F X)
}.
Proof. cat. Defined.

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
    (*@comp (FunCat C D) _ _ _ α β == @id (FunCat C D) F /\
    @comp (FunCat C D) _ _ _ β α == @id (FunCat C D) G.*)

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
        rewrite H3 in H4. repeat rewrite comp_assoc in H4.
        rewrite H0 in H4. cat.
    destruct component_β as [component_β [inverse_α_β coherence_β]].
    eexists {| component := component_β; coherence := coherence_β |}.
    cat; apply inverse_α_β.
Defined.

Instance FunCat_prodOb {C D : Cat} {hp : has_products D}
    (F G : Functor C D) : Functor C D :=
{
    fob := fun X : Ob C => prodOb (fob F X) (fob G X);
    fmap := fun (X Y : Ob C) (f : Hom X Y) =>
      ProductFunctor_fmap (fmap F f) (fmap G f)
}.
Proof.
  repeat red; intros. destruct hp. simpl in *.
    rewrite H. reflexivity.
  intros. pose (H := ProductFunctor_fmap_pres_comp D hp).
    destruct F, G, hp. simpl in *.
    rewrite pres_comp, pres_comp0, H. reflexivity.
  intros. pose (H := ProductFunctor_fmap_pres_id D hp).
    destruct F, G, hp. simpl in *.
    rewrite pres_id, pres_id0, H. reflexivity.
Defined.

Instance FunCat_proj1 {C D : Cat} {hp : has_products D}
    {F G : Functor C D} : NatTrans (FunCat_prodOb F G) F :=
{
    component := fun _ : Ob C => proj1
}.
Proof.
  intros. destruct hp. simpl in *.
  do 2 red in is_product.
  destruct (is_product _ _ _
    (proj1 (fob F X) (fob G X) .> fmap F f)
    (proj2 (fob F X) (fob G X) .> fmap G f)).
  destruct H as [H1 H2]. exact H1.
Defined.

Instance FunCat_proj2 {C D : Cat} {hp : has_products D}
    {F G : Functor C D} : NatTrans (FunCat_prodOb F G) G :=
{
    component := fun _ : Ob C => proj2
}.
Proof.
  intros. destruct hp. simpl in *.
  do 2 red in is_product.
  destruct (is_product _ _ _
    (proj1 (fob F X) (fob G X) .> fmap F f)
    (proj2 (fob F X) (fob G X) .> fmap G f)).
  destruct H as [H1 H2]. exact H2.
Defined.

Instance FunCat_fpair (* TODO *)
    {C D : Cat} {hp : has_products D} {F G H : Functor C D}
    (α : NatTrans F G) (β : NatTrans F H) : NatTrans F (FunCat_prodOb G H) :=
{
    component := fun X : Ob C => fpair (component α X) (component β X)
}.
Proof.
  intros. destruct α, β; simpl in *.
  unfold ProductFunctor_fmap.
  destruct F, G, H; simpl in *.
  destruct hp; simpl in *.
  do 2 red in is_product.
Abort.

(* TODO *)
Instance has_products {C D : Cat} {hp : has_products D}
    : has_products (FunCat C D) :=
{
    prodOb := FunCat_prodOb;
    proj1 := @FunCat_proj1 C D hp;
    proj2 := @FunCat_proj2 C D hp;
    (*fpair := fun (G H F : Functor C D)
      (α : @Hom (FunCat C D) F G) (β : @Hom (FunCat C D) F H)
      => @FunCat_fpair C D hp F G H α β*)
}.
Proof.
Abort.