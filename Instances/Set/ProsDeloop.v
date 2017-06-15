Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Require Export Instances.Set.Pros.

Instance DeloopPros (P : Pros) : Cat :=
{
    Ob := carrier;
    Hom := leq;
    HomSetoid := fun (X Y : carrier) =>
      {| equiv := fun f g : X ≤ Y => True |}; (* Proof irrelevance *)
    comp := leq_trans;
    id := leq_refl
}.
Proof.
  (* Equivalence *) solve_equiv.
  (* composition is proper *) proper.
  (* Category laws *) all: cat.
Defined.

