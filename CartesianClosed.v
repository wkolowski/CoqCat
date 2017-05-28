Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Import InitTerm.
Require Import Cat.BinProdCoprod.
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
    (ht : has_term C) (hp : has_products C),
        prodOb (term C) X ~ X.
Proof.
  symmetry.
  red. exists (fpair (delete X) (id X)).
  red. exists proj2. split.
    apply fpair_proj2.
    rewrite fpair_pre. rewrite <- fpair_id. apply fpair_Proper.
      rewrite (is_terminal _ proj1). cat.
      cat.
Qed.

Theorem prod_term_iso_r : forall (C : Cat) (X : Ob C)
    (ht : has_term C) (hp : has_products C),
        prodOb X (term C) ~ X.
Proof.
  intros. rewrite prodOb_comm. apply prod_term_iso_l.
Qed.

Theorem coprod_init_iso_l : forall (C : Cat) (X : Ob C)
  (hi : has_init C) (hp : has_coproducts C),
    coprodOb (init C) X ~ X.
Proof.
  intros.
  red. exists (copair (create X) (id X)).
  red. exists coproj2. split.
    rewrite copair_post. rewrite <- copair_id. apply copair_Proper.
      rewrite (is_initial _ coproj1). cat.
      cat.
    apply copair_coproj2.
Qed.

Theorem coprod_init_iso_r : forall (C : Cat) (X : Ob C)
  (hi : has_init C) (hp : has_coproducts C),
    coprodOb X (init C) ~ X.
Proof.
  intros. rewrite coprodOb_comm. apply coprod_init_iso_l.
Qed.

(* TODO *) Theorem exp_term_dom :
    forall (C : Cat) (ccc : cartesian_closed C) (Y : Ob C),
    expOb (term C) Y ~ Y.
Proof.
  symmetry.
  red. exists (curry proj1).
  red. exists (fpair (id (expOb (term C) Y)) (delete _) .> eval).
  split.
    fpair. SearchAbout eval.

 SearchAbout id. replace Y with (prodOb Y (term C)).
      rewrite <- fpair_id. SearchAbout fpair.
      SearchAbout curry.


  destruct ccc, ccc_term0, ccc_prod0, ccc_exp0; simpl in *.
  do 2 red in is_exponential; simpl in *.
Abort.

(* TODO *) Theorem exp_term_cod :
    forall (C : Cat) (ccc : cartesian_closed C) (Y : Ob C),
    expOb Y (term C) ~ term C.
Proof.
  intros.
  red. exists (delete _).
  red. exists (curry proj1).
  split.
    Focus 2. destruct ccc, ccc_term0; simpl in *.
      rewrite is_terminal. rewrite <- (is_terminal _ (id term)).
        reflexivity.
    pose (unc := @uncurry C ccc_prod ccc_exp).
    assert (forall (A B C : Ob C) (f : Hom C (expOb A B)),
      curry (unc _ _ _ f) == f).
      intros. unfold unc. rewrite curry_uncurry. reflexivity.
    unfold uncurry in *.
    destruct ccc, ccc_term0, ccc_exp0; simpl in *.
    do 2 red in is_exponential; simpl in *.
 (*   unfold uncurry in unc. simpl in unc.*)
    destruct (is_exponential _ _ (expOb Y term)
      (unc _ _ _ (delete (expOb Y term) .> curry Y term term proj1)))
      as [H1 H2].
    specialize (H2 (id _)). rewrite <- H2. rewrite H. reflexivity.
    rewrite <- H1. unfold ProductFunctor_fmap. rewrite H1.
Abort.