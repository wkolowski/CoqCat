From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct.

#[refine]
#[export]
Instance Discrete (X : Type) : Cat :=
{
  Ob := X;
  Hom := fun x x' : X => x = x';
  HomSetoid := fun (x x' : X) => {| equiv := fun H H' : x = x' => True |};
  comp := @eq_trans X;
  id := @eq_refl X
}.
Proof.
  - now solve_equiv.
  - now proper.
  - easy.
  - easy.
  - easy.
Defined.

#[export] Instance Empty : Cat := Discrete Empty_set.
#[export] Instance Unit : Cat := Discrete unit.

Lemma Discrete_char_iso :
  forall (X : Type) (x x' : X) (f : @Hom (Discrete X) x x'),
    isIso f.
Proof.
  now unfold isIso; cbn.
Defined.

#[refine]
#[export]
Instance Two : Cat :=
{
  Ob := bool;
  Hom := fun b b' : bool => if eqb b b' then True else False;
  HomSetoid := fun b b' : bool => {| equiv := fun _ _ => True |}
}.
Proof.
  - now solve_equiv.
  - now intros [] [] [].
  - now proper.
  - now intros [] [] [] [].
  - now intros [].
  - now intros [] [].
  - now intros [] [].
Defined.