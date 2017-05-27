Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import BinProdCoprod.
Require Import InitTerm.

Definition distr
  {C : Cat} {hi : has_init C} {ht : has_term C}
  {hp : has_products C} {hc : has_coproducts C} (X Y Z : Ob C)
  : Hom (coprodOb (prodOb X Y) (prodOb X Z)) (prodOb X (coprodOb Y Z))
  := copair
    (fpair proj1 (proj2 .> coproj1))
    (fpair proj1 (proj2 .> coproj2)).

Class distributive (C : Cat) : Type :=
{
    distr_has_init :> has_init C;
    distr_has_term :> has_term C;
    distr_has_products :> has_products C;
    distr_has_coproducts :> has_coproducts C;
    distr_iso : forall X Y Z : Ob C, Iso (distr X Y Z)
}.

(* TODO *) Theorem distr_prodOb_init :
  forall (C : Cat) (d : distributive C) (X : Ob C),
    prodOb (init C) X ~ init C.
Proof.
  intros.
  red. exists proj1.
  red. exists (fpair (id _) (create _)).
  split.
    Focus 2. fpair.
    fpair. rewrite <- fpair_id. apply fpair_Proper.
      reflexivity.
      
    



    pose (mor_to_init_is_ret C (init C) (prodOb (init C) X) proj1).
    assert (initial (init C)).
      red. intros. exists (create X0). repeat red. split; auto.
      intros. rewrite <- is_initial. reflexivity.
    specialize (r H). assert (H' : @Epi C (prodOb (init C) X) _ proj1).
      apply ret_is_epi. assumption.
    destruct r as [x H0].
    assert (x .> proj1 .> create X == x .> proj2).
      rewrite H0. rewrite id_left. rewrite (is_initial _ (x .> proj2)).
      reflexivity.
    unfold Epi in H'.
    assert (x == create (prodOb (init C) X)).
      rewrite is_initial. reflexivity.
      assert (create (prodOb (init C) X)
        == fpair (id (init C)) (create X)).
        edestruct is_product. rewrite H4.
          reflexivity.
          split.
            rewrite <- is_initial. cat.
            rewrite <- is_initial. cat.
      assert (create X == create (prodOb (init C) X) .> proj2).
        rewrite H3. fpair.
        rewrite H4. rewrite H3. assocl. rewrite fpair_pre. 
   

    assert (x .> proj1 .> fpair (id (init C)) (create X)
      == x .> id (prodOb (init C) X)).
      rewrite H0. cat. rewrite is_initial.
      (*estruct hi. simpl in *.*) rewrite (is_initial _ x). trivial.
(*    destruct d, distr_has_products. simpl in *.
    do 2 red in is_product.
    destruct (is_product _ _ _ (create (init C)) (create X)) as [[H1' H2'] H3'].
  *)


    rewrite H0 in H1. rewrite H0 in H2. cat.
Restart.
  intros. symmetry.
  red. exists (create _).
  red. exists (proj1).
  split.
    rewrite is_initial. rewrite <- is_initial. reflexivity.
    rewrite <- fpair_id.
      (*destruct d, distr_has_products. simpl in *.*)
 (*     do 2 red in is_product.*)
      destruct (is_product _ _ _ (create (init C)) (create X)) as [[H1 H2] H3].
        rewrite <- H3.
          rewrite fpair_pre. apply fpair_Proper.
            assert (create (init C) == id (init C)).
              rewrite <- is_initial. reflexivity.
              rewrite H. cat.
            destruct d, distr_has_products. simpl in *.
            do 2 red in is_product. Print Ret.
            destruct (is_product _ _ _ proj1 proj2).
            rewrite H2. assocl. rewrite fpair_pre.









