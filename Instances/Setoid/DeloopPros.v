From Cat Require Export Cat.
From Cat.Limits Require Export Initial Terminal Product Coproduct.
From Cat Require Export Instances.Setoid.Pros.

#[refine]
#[export]
Instance DeloopPros (P : Pros) : Cat :=
{
  Ob := carrier;
  Hom := leq;
  HomSetoid := fun (X Y : carrier) => {| equiv := fun f g : X ≤ Y => True |};
  comp := leq_trans;
}.
Proof. all: pros. Defined.