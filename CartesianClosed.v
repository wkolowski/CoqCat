Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.
Require Import Exponential.

Class cartesian_closed (C : Cat) : Type :=
{
    ccc_term :> has_term C;
    ccc_prod :> has_products C;
    ccc_exp :> has_exponentials C
}.

Arguments term [C] [has_term].
Arguments delete [C] [has_term] _.
Arguments diag [C] [has_products] _ _ _ _ _.

Theorem id_unique_left' : forall (C : Cat) (X Y : Ob C)
    (f : Hom X Y) (g : Hom Y X), f .> g .> f == f -> f .> g == id X.
Proof.
  intros. apply id_unique_left. intros.

Theorem prod_term_iso : forall (C : Cat) (X : Ob C)
    (ht : has_term C) (hp : has_products C),
        prodOb term X ~ X.
Proof.
  symmetry. (*destruct ht, hp*) intros; red; simpl.
  pose (f := diag term X X (delete X) (id X)).
  exists f; red. exists (proj2 term X). unfold f.
  destruct (is_product term X X (delete X) (id X)) as [[H1 H2] H3].
  split.
    rewrite <- H2. reflexivity.
    assert (diag term X X (delete X) (id X) .> proj2 term X
      .> diag term X X (delete X) (id X) ==
      diag term X X (delete X) (id X)).
        rewrite <- H2, id_left. reflexivity.
Check id_unique_left. apply id_unique_left. intros.
    rewrite comp_assoc. 
    destruct (is_product term X (prodOb term X) (delete _) (proj2 term X)).
      destruct H0. specialize (H4 (id _)). cat.
      assert (delete (prodOb term X) == proj1 term X).
      destruct ht. simpl in *. rewrite <- is_terminal. reflexivity.
      
      destruct (is_terminal (prodOb term X) (proj1 term X)).



    rewrite <- ProductFunctor_fmap_pres_id.
      unfold ProductFunctor_fmap.
      