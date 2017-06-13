Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Require Export Instances.Set.Mon.

Instance DeloopMon (M : Mon) : Cat :=
{
    Ob := unit;
    Hom := fun _ _ => @carrier M;
    HomSetoid := fun _ _ =>
      {| equiv := eq |};
    comp := fun _ _ _ => @op M;
    id := fun _ => @neutr M
}.
Proof.
  (* Equivalence *) solve_equiv.
  (* composition is proper *) intros. simpl. rewrite neutr_l. trivial.
  (* Category laws *) all: cat.
Defined.

