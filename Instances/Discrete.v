From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct.

#[refine]
#[export]
Instance Discrete (X : Set) : Cat :=
{
  Ob := X;
  Hom := fun x x' : X => x = x';
  HomSetoid := fun (x x' : X) => {| equiv := fun H H' : x = x' => True |};
  comp := @eq_trans X;
  id := @eq_refl X
}.
Proof.
  (* Equivalence *) solve_equiv.
  (* composition is proper *) proper.
  (* Category laws *) all: cat.
Defined.

#[export] Instance Empty : Cat := Discrete Empty_set.
#[export] Instance Unit : Cat := Discrete unit.

Lemma Discrete_char_iso :
  forall (X : Set) (x x' : X) (f : @Hom (Discrete X) x x'),
    isIso f.
Proof.
  unfold isIso; cbn; intros X x x' ->.
  now exists eq_refl.
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
  (* Equivalence *) solve_equiv.
  (* Composition *) now destruct A, B, C.
  (* Proper *) proper.
  (* Assoc *) cat.
  (* Id *) now destruct A.
  (* Id laws *) all: cat.
Defined.