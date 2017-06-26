Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Cat.Cat.

Require Import Cat.Limits.BinProdCoprod.

Set Implicit Arguments.

Class Bifunctor (C D E: Cat) : Type :=
{
    biob : Ob C -> Ob D -> Ob E;
    bimap : forall {X Y : Ob C} {X' Y' : Ob D},
        Hom X Y -> Hom X' Y' -> Hom (biob X X') (biob Y Y');
    bimap_Proper :> forall (X Y : Ob C) (X' Y' : Ob D),
        Proper (equiv ==> equiv ==> equiv) (@bimap X Y X' Y');
    bimap_pres_comp : forall (X Y Z : Ob C) (X' Y' Z' : Ob D)
      (f : Hom X Y) (g : Hom Y Z) (f' : Hom X' Y') (g' : Hom Y' Z'),
        bimap (f .> g) (f' .> g') == bimap f f' .> bimap g g';
    bimap_pres_id : forall (X : Ob C) (Y : Ob D),
        bimap (id X) (id Y) == id (biob X Y);
}.

Arguments biob [C D E Bifunctor] _ _.
Arguments bimap [C D E Bifunctor X Y X' Y'] _ _.

Instance ProductBifunctor {C : Cat} {hp : has_products C} :
    Bifunctor C C C :=
{
    biob := fun X Y : Ob C => prodOb X Y;
    bimap := fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') =>
      fpair (proj1 .> f) (proj2 .> g);

}.
Proof.
  unfold Proper, respectful. all: fpair.
Defined.

Instance CoproductBifunctor {C : Cat} {hp : has_coproducts C} :
    Bifunctor C C C :=
{
    biob := @coprodOb C hp;
    bimap := fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') =>
      copair (f .> coproj1) (g .> coproj2)
}.
Proof.
  unfold Proper, respectful. all: copair.
Defined.

Instance BiComp {C C' D D' E : Cat}
    (B : Bifunctor C' D' E) (F : Functor C C') (G : Functor D D')
    : Bifunctor C D E :=
{
    biob := fun (X : Ob C) (Y : Ob D) => biob (fob F X) (fob G Y);
    bimap := fun (X Y : Ob C) (X' Y' : Ob D) (f : Hom X Y) (g : Hom X' Y') =>
      bimap (fmap F f) (fmap G g)
}.
Proof.
  proper.
  intros. repeat rewrite pres_comp; repeat rewrite bimap_pres_comp.
    reflexivity.
  intros. do 2 rewrite pres_id. rewrite bimap_pres_id.
    reflexivity.
Defined.

Instance Const {E : Cat} (X : Ob E) (C D : Cat)
    : Bifunctor C D E :=
{
    biob := fun _ _ => X;
    bimap := fun _ _ _ _ _ _ => id X
}.
Proof. proper. all: cat. Defined.