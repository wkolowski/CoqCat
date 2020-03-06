Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

#[refine]
Instance Discrete (X : Set) : Cat :=
{
    Ob := X;
    Hom := fun x x' : X => x = x';
    HomSetoid := fun (x x' : X) =>
      {| equiv := fun H H' : x = x' => True |}; (* Proof irrelevance *)
    comp := @eq_trans X;
    id := @eq_refl X
}.
Proof.
  (* Equivalence *) solve_equiv.
  (* composition is proper *) proper.
  (* Category laws *) all: cat.
Defined.

Instance Empty : Cat := Discrete Empty_set.
Instance Unit : Cat := Discrete unit.

Theorem Discrete_char_iso : forall (X : Set) (x x' : X)
    (f : @Hom (Discrete X) x x'), Iso f.
Proof.
  unfold Iso; simpl; intros. assert (g : x' = x).
    rewrite f. trivial.
    exists g. auto.
Defined.

Require Import Bool.

#[refine]
Instance Two : Cat :=
{
    Ob := bool;
    Hom := fun b b' : bool => if eqb b b' then True else False;
    HomSetoid := fun b b' : bool =>
      {| equiv := fun _ _ => True |}
}.
Proof.
  (* Equivalence *) solve_equiv.
  (* Composition *) destruct A, B, C; simpl; tauto.
  (* Proper *) proper.
  (* Assoc *) cat.
  (* Id *) destruct A; simpl; tauto.
  (* Id laws *) all: cat.
Defined.