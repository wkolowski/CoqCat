Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Set Universe Polymorphism.

Instance Discrete (X : Set) : Cat :=
{
    Ob := X;
    Hom := fun x x' : X => x = x';
    HomSetoid := fun (x x' : X) =>
      {| equiv := fun H H' : x = x' => True |}; (* Proof irrelevance *)
    comp := @eq_trans X;
    id := @eq_refl X
}.
Proof. all: cat. Defined.

Eval compute in Discrete Empty_set.

Instance Empty : Cat := Discrete Empty_set.
Instance Unit : Cat := Discrete unit.

Theorem Discrete_char_iso : forall (X : Set) (x x' : X)
    (f : @Hom (Discrete X) x x'), Iso f.
Proof.
  unfold Iso; simpl; intros. assert (g : x' = x).
    rewrite f. auto.
  exists g. auto.
Defined.


