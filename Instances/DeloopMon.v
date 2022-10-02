From Cat Require Import Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct.
From Cat Require Import Instances.Mon.

#[refine]
#[export]
Instance DeloopMon (M : Mon) : Cat :=
{
  Ob := unit;
  Hom := fun _ _ => @carrier M;
  HomSetoid := fun _ _ => {| equiv := equiv |};
  comp := fun _ _ _ => @op M;
  id := fun _ => @neutr M
}.
Proof. all: now mon. Defined.