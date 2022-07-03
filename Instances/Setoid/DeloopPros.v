From Cat Require Export Cat.
From Cat Require Export Limits.InitTerm.
From Cat Require Export Limits.BinProdCoprod.
From Cat Require Export Instances.Setoid.Pros.

#[refine]
#[export]
Instance DeloopPros (P : Pros) : Cat :=
{
  Ob := carrier;
  Hom := leq;
  HomSetoid := fun (X Y : carrier) =>
    {| equiv := fun f g : X ≤ Y => True |}; (* Proof irrelevance *)
  comp := leq_trans;
}.
Proof. all: pros. Defined.