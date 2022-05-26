Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

#[refine]
#[export]
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

#[export]
Instance Empty : Cat := Discrete Empty_set.
#[export]
Instance Unit : Cat := Discrete unit.

Theorem Discrete_char_iso : forall (X : Set) (x x' : X)
    (f : @Hom (Discrete X) x x'), Iso f.
Proof.
  unfold Iso; cbn; intros. assert (g : x' = x).
    rewrite f. trivial.
    exists g. auto.
Defined.

Require Import Bool.

#[refine]
#[export]
Instance Two : Cat :=
{
    Ob := bool;
    Hom := fun b b' : bool => if eqb b b' then True else False;
    HomSetoid := fun b b' : bool =>
      {| equiv := fun _ _ => True |}
}.
Proof.
  (* Equivalence *) solve_equiv.
  (* Composition *) destruct A, B, C; cbn; tauto.
  (* Proper *) proper.
  (* Assoc *) cat.
  (* Id *) destruct A; cbn; tauto.
  (* Id laws *) all: cat.
Defined.