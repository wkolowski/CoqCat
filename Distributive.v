From Cat Require Import BinProdCoprod.
From Cat Require Import InitTerm.

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
  intros. symmetry.
  red. exists (create _).
  red. exists (proj1).
  split.
    init.
    rewrite <- fpair_id.
      destruct (is_product _ _ _ (create (init C)) (create X)) as [[H1 H2] H3].
        rewrite <- H3.
          rewrite fpair_pre. apply fpair_Proper.
            assert (create (init C) == id (init C)). init.
              rewrite H. cat.
            destruct d, distr_has_products. cbn in *.
            do 2 red in is_product.
Abort.