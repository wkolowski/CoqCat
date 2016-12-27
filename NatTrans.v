Require Export Functor.
Require Export BinProdCoprod.

Set Primitive Projections.

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

Instance NatTransComp {C D : Cat} (F : Functor C D) (G : Functor C D)
    (H : Functor C D) (alfa : NatTrans F G) (beta : NatTrans G H)
    : NatTrans F H :=
{
    component := fun X : Ob C => component alfa X .> component beta X
}.
Proof.
  intros. destruct alfa, beta; simpl in *. repeat rewrite comp_assoc.
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
    Hom := NatTrans;
    HomSetoid := fun F G : Functor C D => NatTransSetoid F G;
    comp := NatTransComp;
    id := NatTransId
}.
Proof.
  (* Proper *) do 3 red; simpl; intros. rewrite H, H0. reflexivity.
  (* Category laws *) all: cat.
Defined.

Definition natural_isomorphism {C D : Cat} {F G : Functor C D}
    (α : NatTrans F G) : Prop := exists β : NatTrans G F,
    (*NatTransComp _ _ _ alfa beta = NatTransId F /\
    NatTransComp _ _ _ beta alfa = NatTransId G.*)
    @comp (FunCat C D) _ _ _ α β == @id (FunCat C D) F /\
    @comp (FunCat C D) _ _ _ β α == @id (FunCat C D) G.

(* Case analysis on sort Type... bla bla *)
Theorem natural_isomorphism_char : forall (C D : Cat) (F G : Functor C D)
    (α : NatTrans F G),
    natural_isomorphism α <-> forall X : Ob C, Iso (component α X).
Proof.
  unfold natural_isomorphism; split; simpl; intros.
    destruct H as [β [Η1 Η2]]. red. exists (component β X). auto.
    assert (componentβ : forall X : Ob C, Hom (fob G X) (fob F X)).
      destruct α; simpl in H. intro. destruct (H X). TODO *)
Abort.
Print has_products.
Print Functor.
Print diag.

Instance FunCat_prodOb {C D : Cat} {hp : has_products D}
    (F G : Functor C D) : Functor C D :=
{
    fob := fun X : Ob C => prodOb (fob F X) (fob G X);
    fmap := fun (X Y : Ob C) (f : Hom X Y) =>
      ProductFunctor_fmap (fmap F f) (fmap G f)
}.
Proof. Print ProductFunctor.
  repeat red; intros. destruct hp. simpl in *.
    rewrite H. reflexivity.
  intros. destruct F, G. simpl in *.
    pose (H := ProductFunctor_fmap_pres_comp).
    destruct hp. simpl in *. rewrite pres_comp0.
   apply ProductFunctor_fmap_pres_comp.
  intros. apply ProductFunctor_fmap_pres_id.
Qed.
  


Instance has_products {C D : Cat} {hp : has_products D}
    : has_products (FunCat C D) :=
Proof.
  esplit. all: admit.
      
    