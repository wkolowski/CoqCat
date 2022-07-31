From Cat.Limits Require Import InitTerm ProdCoprod.

Definition distr
  {C : Cat} {hi : HasInit C} {ht : HasTerm C}
  {hp : HasProducts C} {hc : HasCoproducts C} (X Y Z : Ob C)
  : Hom (coprodOb (prodOb X Y) (prodOb X Z)) (prodOb X (coprodOb Y Z))
  := copair (fpair proj1 (proj2 .> coproj1)) (fpair proj1 (proj2 .> coproj2)).

Class Distributive (C : Cat) : Type :=
{
  HasInit_Distributive :> HasInit C;
  HasTerm_Distributive :> HasTerm C;
  HasProducts_Distributive :> HasProducts C;
  HasCoproducts_Distributive :> HasCoproducts C;
  Iso_distr : forall X Y Z : Ob C, Iso (distr X Y Z)
}.

(* TODO *) Lemma distr_prodOb_init :
  forall (C : Cat) (d : Distributive C) (X : Ob C),
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
          rewrite fpair_pre. apply Proper_fpair.
            assert (create (init C) == id (init C)). init.
              rewrite H. cat.
            destruct d, HasProducts_Distributive. cbn in *.
            do 2 red in is_product.
Abort.