Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".
Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/Instances".

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Require Export Pros.

Set Universe Polymorphism.

Instance DeloopPros (P : Pros) : Cat :=
{
    Ob := carrier;
    Hom := leq;
    HomSetoid := fun (X Y : carrier) =>
      {| equiv := fun f g : X ≤ Y => True |}; (* Proof irrelevance *)
    comp := leq_trans;
    id := leq_refl
}.
Proof. all: cat. Defined.

