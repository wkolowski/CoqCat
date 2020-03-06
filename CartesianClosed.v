Require Export Cat.
Require Import Limits.InitTerm.
Require Import Limits.BinProdCoprod.
Require Import Exponential.

Class cartesian_closed (C : Cat) : Type :=
{
    ccc_term :> has_term C;
    ccc_prod :> has_products C;
    ccc_exp :> has_exponentials C
}.

Coercion ccc_term : cartesian_closed >-> has_term.
Coercion ccc_prod : cartesian_closed >-> has_products.
Coercion ccc_exp : cartesian_closed >-> has_exponentials.

Theorem prod_term_iso_l : forall (C : Cat) (X : Ob C)
  (ht : has_term C) (hp : has_products C), prodOb (term C) X ~ X.
Proof.
  symmetry.
  red. exists (fpair (delete X) (id X)).
  red. exists proj2.
  fpair. term.
Defined.

Theorem prod_term_iso_l' :
  forall (C : Cat) (X : Ob C) (ht : has_term C) (hp : has_products C),
    {f : Hom (prodOb (term C) X) X | Iso f}.
Proof.
  intros. exists proj2.
  red. exists (fpair (delete X) (id X)). fpair. term.
Defined.

Theorem prod_term_iso_r : forall (C : Cat) (X : Ob C)
  (ht : has_term C) (hp : has_products C), prodOb X (term C) ~ X.
Proof.
  intros. rewrite prodOb_comm. apply prod_term_iso_l.
Defined.

Theorem prod_term_iso_r' :
  forall (C : Cat) (X : Ob C) (ht : has_term C) (hp : has_products C),
    {f : Hom (prodOb X (term C)) X | Iso f}.
Proof.
  intros. exists proj1.
  red. exists (fpair (id X) (delete X)). fpair. term.
Defined.

Theorem coprod_init_iso_l : forall (C : Cat) (X : Ob C)
  (hi : has_init C) (hp : has_coproducts C), coprodOb (init C) X ~ X.
Proof.
  intros.
  red. exists (copair (create X) (id X)).
  red. exists coproj2.
  copair. init.
Defined.

Theorem coprod_init_iso_l' :
  forall (C : Cat) (X : Ob C) (hi : has_init C) (hp : has_coproducts C),
    {f : Hom (coprodOb (init C) X) X | Iso f}.
Proof.
  intros.
  exists (copair (create X) (id X)).
  red. exists coproj2.
  copair. init.
Defined.

Theorem coprod_init_iso_r : forall (C : Cat) (X : Ob C)
  (hi : has_init C) (hp : has_coproducts C), coprodOb X (init C) ~ X.
Proof.
  intros. rewrite coprodOb_comm. apply coprod_init_iso_l.
Qed.

Theorem coprod_init_iso_r' :
  forall (C : Cat) (X : Ob C) (hi : has_init C) (hp : has_coproducts C),
    {f : Hom (coprodOb X (init C)) X | Iso f}.
Proof.
  intros.
  exists (copair (id X) (create X)).
  red. exists coproj1.
  copair. init.
Defined.

(* TODO *)
Theorem exp_term_dom :
  forall (C : Cat) (ccc : cartesian_closed C) (Y : Ob C),
    expOb (term C) Y ~ Y.
Proof.
  symmetry.
  red. exists (curry proj1).
  red. exists (fpair (id (expOb (term C) Y)) (delete _) .> eval).
  split.
    Focus 2. 
Abort.

Lemma wuuut :
  forall (C : Cat) (ccc : cartesian_closed C) (X Y A : Ob C)
  (f : Hom A (expOb X Y)) (g : Hom A X),
    fpair f g .> eval .> curry proj1 == f.
Proof.
  intros. destruct ccc, ccc_term0, ccc_prod0, ccc_exp0. cbn in *.
    do 2 red in is_exponential.
    do 2 red in is_product. unfold ProductFunctor_fmap in is_exponential. cbn in *.
Abort.

(* TODO *) Theorem exp_term_cod :
    forall (C : Cat) (ccc : cartesian_closed C) (Y : Ob C),
    expOb Y (term C) ~ term C.
Proof.
  intros.
  red. exists (delete _).
  red. exists (curry proj1).
  split.
    Focus 2. term.
    (*pose (mor_from_term_is_sec C _ _ (@curry C ccc ccc Y (term C) (term C) proj1)).
    assert (terminal (term C)).
      red. intros. exists (delete _). cat. term.
    specialize (s H). destruct s as [g is_sec].
    assert (delete _ .> curry proj1 .> g == g).
      assocr. rewrite is_sec. term.    
    assert (@curry C ccc ccc Y (term C) (term C) proj1
      .> delete _ .> curry proj1 .> g == curry proj1 .> g).
      assocr'. rewrite is_sec. term.
    rewrite !comp_assoc, is_sec in H1.
    cat.*)
Abort.