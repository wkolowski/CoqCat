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
  forall (C : Cat) (hi : has_init C) (d : distributive C) (X : Ob C),
    prodOb (init C) X ~ init C.
Proof.
  intros.
  red. exists proj1.
  red. exists (fpair (id _) (create _)).
  split.
    rewrite fpair_pre, <- fpair_id. apply fpair_Proper.
      cat.
      destruct hi, d; simpl.
Abort.