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

Theorem prod_term_iso : forall (C : Cat) (X : Ob C)
    (ht : has_term C) (hp : has_products C),
        prodOb (term C) X ~ X.
Proof.
  symmetry.
  red. pose (f := fpair (delete X) (id X)). exists f.
  red. exists proj2. unfold f. split.
    destruct hp; simpl in *. do 2 red in is_product.
      destruct (is_product (term C) X X (delete X) (id X)) as [[H1 H2] H3].
      rewrite <- H2. reflexivity.
    assert (forall (Y : Ob C) (y : Hom Y (prodOb (term C) X)),
      y .> proj2 .> fpair (delete X) (id X) == y).
      intros. destruct hp; do 2 red in is_product; simpl in *.
        destruct (is_product (term C) X Y (y .> proj1 _ _) (y .> proj2 _ _))
        as [[H1 H2] H3].
        rewrite H2. specialize (H3 y).
Abort.

Theorem exp_term_dom :
    forall (C : Cat) (ccc : cartesian_closed C) (Y : Ob C),
    expOb (term C) Y ~ Y.
Proof.
  symmetry; red.
  exists (curry proj1). red.
  exists (fpair (id (expOb (term C) Y)) (delete _) .> eval).
  destruct ccc, ccc_term0, ccc_prod0, ccc_exp0; simpl in *.
  do 2 red in is_exponential; simpl in *.
  split.
Abort.

Theorem exp_term_cod :
    forall (C : Cat) (ccc : cartesian_closed C) (Y : Ob C),
    expOb Y (term C) ~ term C.
Proof.
  red; intros.
  exists (delete _). red. exists (curry proj1).
  split.
    Focus 2. destruct ccc, ccc_term0; simpl in *.
      rewrite is_terminal. rewrite <- (is_terminal _ (id term)).
        reflexivity.
    destruct ccc, ccc_term0; simpl in *.
    destruct ccc_exp0; do 2 red in is_exponential; simpl in *.
    destruct (is_exponential Y term (expOb Y term) (eval _ _)).
      specialize (H0 (id (expOb Y term))).
      rewrite <- H0.
Abort.