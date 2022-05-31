From Cat Require Import Cat.
From Cat Require Import Limits.InitTerm.
From Cat Require Import Limits.BinProdCoprod.
From Cat Require Import Instances.Setoid.Mon.

#[refine]
#[export]
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