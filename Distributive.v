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
      
    



    (*pose (mor_to_init_is_ret C (init C) (prodOb (init C) X) proj1).
    assert (initial (init C)).
      red. intros. exists (create X0). repeat red. split; auto.
      init.
    specialize (r H). assert (H' : @Epi C (prodOb (init C) X) _ proj1).
      apply ret_is_epi. assumption.
    destruct r as [x H0].
    assert (x .> proj1 .> create X == x .> proj2).
      init.
    unfold Epi in H'.
    assert (x == create (prodOb (init C) X)).
      init.
      assert (create (prodOb (init C) X)
        == fpair (id (init C)) (create X)).
        init.
      assert (create X == create (prodOb (init C) X) .> proj2).
        init.

    assert (x .> proj1 .> fpair (id (init C)) (create X)
      == x .> id (prodOb (init C) X)).
      init.*)
Restart.
  intros. symmetry.
  red. exists (create _).
  red. exists (proj1).
  split.
    init.
    rewrite <- fpair_id.
      (*destruct d, distr_has_products. simpl in *.*)
 (*     do 2 red in is_product.*)
      destruct (is_product _ _ _ (create (init C)) (create X)) as [[H1 H2] H3].
        rewrite <- H3.
          rewrite fpair_pre. apply fpair_Proper.
            assert (create (init C) == id (init C)). init.
              rewrite H. cat.
            destruct d, distr_has_products. simpl in *.
            do 2 red in is_product.
Abort.