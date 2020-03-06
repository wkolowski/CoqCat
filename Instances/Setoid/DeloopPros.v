Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Require Export Instances.Setoid.Pros.

#[refine]
Instance DeloopPros (P : Pros) : Cat :=
{
    Ob := carrier;
    Hom := leq;
    HomSetoid := fun (X Y : carrier) =>
      {| equiv := fun f g : X ≤ Y => True |}; (* Proof irrelevance *)
    comp := leq_trans;
(*    id := fun x => leq_refl x x (equiv_refl)*)
}.
Proof. all: pros. Defined.