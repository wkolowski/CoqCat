From Cat Require Export Cat.
From Cat Require Export InitTerm.
From Cat Require Export BinProdCoprod.
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
(*    id := fun x => leq_refl x x (equiv_refl)*)
}.
Proof. all: pros. Defined.