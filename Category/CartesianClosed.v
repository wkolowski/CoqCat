From Cat Require Export Cat.
From Cat.Limits Require Import InitTerm ProdCoprod Exponential.

Class CartesianClosed (C : Cat) : Type :=
{
  HasTerm_CartesianClosed :> HasTerm C;
  HasProducts_CartesianClosed :> HasProducts C;
  HasExponentials_CartesianClosed :> HasExponentials C
}.

Coercion HasTerm_CartesianClosed : CartesianClosed >-> HasTerm.
Coercion HasProducts_CartesianClosed : CartesianClosed >-> HasProducts.
Coercion HasExponentials_CartesianClosed  : CartesianClosed >-> HasExponentials.

Lemma prodOb_term_l :
  forall (C : Cat) (ht : HasTerm C) (hp : HasProducts C) (X : Ob C),
    prodOb (term C) X ~ X.
Proof.
  symmetry.
  red. exists (fpair (delete X) (id X)).
  red. exists outr.
  fpair. term.
Defined.

Lemma prodOb_term_l' :
  forall (C : Cat) (ht : HasTerm C) (hp : HasProducts C) (X : Ob C),
    {f : Hom (prodOb (term C) X) X | isIso f}.
Proof.
  intros. exists outr.
  red. exists (fpair (delete X) (id X)). fpair. term.
Defined.

Lemma prodOb_term_r :
  forall (C : Cat) (ht : HasTerm C) (hp : HasProducts C) (X : Ob C),
    prodOb X (term C) ~ X.
Proof.
  intros. rewrite prodOb_comm. apply prodOb_term_l.
Defined.

Lemma prodOb_term_r' :
  forall (C : Cat) (X : Ob C) (ht : HasTerm C) (hp : HasProducts C),
    {f : Hom (prodOb X (term C)) X | isIso f}.
Proof.
  intros. exists outl.
  red. exists (fpair (id X) (delete X)). fpair. term.
Defined.

Lemma coprodOb_init_l :
  forall (C : Cat) (hi : HasInit C) (hp : HasCoproducts C) (X : Ob C),
    coprodOb (init C) X ~ X.
Proof.
  intros.
  red. exists (copair (create X) (id X)).
  red. exists coproj2.
  copair. init.
Defined.

Lemma coprodOb_init_l' :
  forall (C : Cat) (hi : HasInit C) (hp : HasCoproducts C) (X : Ob C),
    {f : Hom (coprodOb (init C) X) X | isIso f}.
Proof.
  intros.
  exists (copair (create X) (id X)).
  red. exists coproj2.
  copair. init.
Defined.

Lemma coprodOb_init_r :
  forall (C : Cat) (hi : HasInit C) (hp : HasCoproducts C) (X : Ob C),
    coprodOb X (init C) ~ X.
Proof.
  intros. rewrite coprodOb_comm. apply coprodOb_init_l.
Qed.

Lemma coprodOb_init_r' :
  forall (C : Cat) (hi : HasInit C) (hp : HasCoproducts C) (X : Ob C),
    {f : Hom (coprodOb X (init C)) X | isIso f}.
Proof.
  intros.
  exists (copair (id X) (create X)).
  red. exists coproj1.
  copair. init.
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
        .> eval) .> curry (X := term C) outl)
    with (curry (uncurry (id (expOb (term C) Y)))).
    + rewrite computation_rule. reflexivity.
    + rewrite !curry_uncurry. admit.
  - rewrite <- comp_assoc, fpair_pre, delete_unique, comp_id_r.
    admit.
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
  - term.
  - rewrite <- curry_eval.
    symmetry.
    apply universal_property. Check curry (delete _).
Abort.