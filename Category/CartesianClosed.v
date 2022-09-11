From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct Exponential.

Class CartesianClosed (C : Cat) : Type :=
{
  HasTerm_CartesianClosed :> HasTerm C;
  HasProducts_CartesianClosed :> HasProducts C;
  HasExponentials_CartesianClosed :> HasExponentials C
}.

Coercion HasTerm_CartesianClosed : CartesianClosed >-> HasTerm.
Coercion HasProducts_CartesianClosed : CartesianClosed >-> HasProducts.
Coercion HasExponentials_CartesianClosed  : CartesianClosed >-> HasExponentials.

Lemma product_term_l :
  forall (C : Cat) (ht : HasTerm C) (hp : HasProducts C) (X : Ob C),
    product (term C) X ~ X.
Proof.
  symmetry.
  red. exists (fpair (delete X) (id X)).
  red. exists outr.
  solve_product; apply equiv_terminal.
Defined.

Lemma product_term_l' :
  forall (C : Cat) (ht : HasTerm C) (hp : HasProducts C) (X : Ob C),
    {f : Hom (product (term C) X) X | isIso f}.
Proof.
  intros.
  exists outr, (fpair (delete X) (id X)).
  solve_product; apply equiv_terminal.
Defined.

Lemma product_term_r :
  forall (C : Cat) (ht : HasTerm C) (hp : HasProducts C) (X : Ob C),
    product X (term C) ~ X.
Proof.
  intros. rewrite product_comm. apply product_term_l.
Defined.

Lemma product_term_r' :
  forall (C : Cat) (X : Ob C) (ht : HasTerm C) (hp : HasProducts C),
    {f : Hom (product X (term C)) X | isIso f}.
Proof.
  intros.
  exists outl, (fpair (id X) (delete X)).
  solve_product; apply equiv_terminal.
Defined.

Lemma coproduct_init_l :
  forall (C : Cat) (hi : HasInit C) (hp : HasCoproducts C) (X : Ob C),
    coproduct (init C) X ~ X.
Proof.
  intros.
  exists (copair (create X) (id X)), finr.
  solve_coproduct; apply equiv_initial.
Defined.

Lemma coproduct_init_l' :
  forall (C : Cat) (hi : HasInit C) (hp : HasCoproducts C) (X : Ob C),
    {f : Hom (coproduct (init C) X) X | isIso f}.
Proof.
  intros.
  exists (copair (create X) (id X)), finr.
  solve_coproduct; apply equiv_initial.
Defined.

Lemma coproduct_init_r :
  forall (C : Cat) (hi : HasInit C) (hp : HasCoproducts C) (X : Ob C),
    coproduct X (init C) ~ X.
Proof.
  intros. rewrite coproduct_comm. apply coproduct_init_l.
Qed.

Lemma coproduct_init_r' :
  forall (C : Cat) (hi : HasInit C) (hp : HasCoproducts C) (X : Ob C),
    {f : Hom (coproduct X (init C)) X | isIso f}.
Proof.
  intros.
  exists (copair (id X) (create X)), finl.
  solve_coproduct; apply equiv_initial.
Defined.

(* TODO *) Lemma exp_term_dom :
  forall (C : Cat) (ccc : CartesianClosed C) (Y : Ob C),
    expOb (term C) Y ~ Y.
Proof.
  symmetry.
  red. exists (curry outl).
  red. exists (fpair (id (expOb (term C) Y)) (delete _) .> eval).
  split; cycle 1.
  - rewrite <- (curry_uncurry (id (expOb (term C) Y))).
    symmetry.
    apply universal_property.
    setoid_replace (
      (fpair (curry (uncurry (id (expOb (term C) Y)))) (delete (expOb (term C) Y))
        .> eval) .> curry (A := term C) outl)
    with (curry (uncurry (id (expOb (term C) Y)))).
    + now rewrite computation_rule.
    + rewrite !curry_uncurry. admit.
  -
Abort.

(* TODO *) Lemma wuuut :
  forall (C : Cat) (ccc : CartesianClosed C) (X Y A : Ob C) (f : Hom A (expOb X Y)) (g : Hom A X),
    fpair f g .> eval .> curry outl == f.
Proof.
Abort.

(* TODO *) Lemma exp_term_cod :
  forall (C : Cat) (ccc : CartesianClosed C) (Y : Ob C),
    expOb Y (term C) ~ term C.
Proof.
  unfold isomorphic, isIso.
  intros.
  exists (delete _), (curry (delete _)).
  split; cycle 1.
  - apply equiv_terminal.
  - rewrite <- curry_eval.
    symmetry.
    apply universal_property.
Abort.