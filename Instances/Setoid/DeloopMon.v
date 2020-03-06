Require Import Cat.
Require Import Cat.Limits.InitTerm.
Require Import Cat.Limits.BinProdCoprod.

Require Import Cat.Instances.Setoid.Mon.

#[refine]
Instance DeloopMon (M : Mon) : Cat :=
{
    Ob := unit;
    Hom := fun _ _ => @carrier M;
    HomSetoid := fun _ _ =>
      {| equiv := equiv |};
    comp := fun _ _ _ => @op M;
    id := fun _ => @neutr M
}.
Proof. all: mon. Defined.