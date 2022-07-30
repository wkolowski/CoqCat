From Cat Require Export Cat.

Set Implicit Arguments.

Class HasProducts (C : Cat) : Type :=
{
  prodOb : Ob C -> Ob C -> Ob C;
  outl : forall {A B : Ob C}, Hom (prodOb A B) A;
  outr : forall {A B : Ob C}, Hom (prodOb A B) B;
  fpair :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (prodOb A B);
  fpair_Proper :>
    forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@fpair A B X);
  comp_l :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B),
      fpair f g .> outl == f;
  comp_r :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B),
      fpair f g .> outr == g;
  unique :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B) (h : Hom X (prodOb A B)),
      h .> outl == f -> h .> outr == g -> h == fpair f g;
}.

Arguments prodOb {C HasProducts} _ _.
Arguments outl   {C HasProducts A B}.
Arguments outr   {C HasProducts A B}.
Arguments fpair  {C HasProducts A B X} _ _.

From Cat.Limits.Equational Require ProdCoprod_Universal.

Module Equiv.

#[refine]
#[export]
Instance to (C : Cat) (hp : HasProducts C) : ProdCoprod_Universal.HasProducts C :=
{
  prodOb := @prodOb C hp;
  outl := @outl C hp;
  outr := @outr C hp;
  fpair := @fpair C hp;
}.
Proof.
  split.
  - intros <-. rewrite comp_l, comp_r. split; reflexivity.
  - intros [-> ->]. symmetry. apply unique; reflexivity.
Defined.

#[refine]
#[export]
Instance from (C : Cat) (hp : ProdCoprod_Universal.HasProducts C) : HasProducts C :=
{
  prodOb := @ProdCoprod_Universal.prodOb C hp;
  outl := @ProdCoprod_Universal.outl C hp;
  outr := @ProdCoprod_Universal.outr C hp;
  fpair := @ProdCoprod_Universal.fpair C hp;
}.
Proof.
  - intros. rewrite ProdCoprod_Universal.fpair_outl. reflexivity.
  - intros. rewrite ProdCoprod_Universal.fpair_outr. reflexivity.
  - intros. symmetry. apply ProdCoprod_Universal.universal.
    split; symmetry; assumption.
Defined.

End Equiv.