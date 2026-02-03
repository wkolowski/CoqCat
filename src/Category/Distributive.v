From Cat.Universal Require Import Initial Terminal Product Coproduct.

Definition distr
  {C : Cat} {hi : HasInit C} {ht : HasTerm C}
  {hp : HasProducts C} {hc : HasCoproducts C} (X Y Z : Ob C)
  : Hom (coproduct (product X Y) (product X Z)) (product X (coproduct Y Z))
  := copair (fpair outl (outr .> finl)) (fpair outl (outr .> finr)).

Class Distributive (C : Cat) : Type :=
{
  HasInit_Distributive :: HasInit C;
  HasTerm_Distributive :: HasTerm C;
  HasProducts_Distributive :: HasProducts C;
  HasCoproducts_Distributive :: HasCoproducts C;
  isIso_distr : forall X Y Z : Ob C, isIso (distr X Y Z)
}.

Lemma distr_product_init :
  forall (C : Cat) (d : Distributive C) (X : Ob C),
    product (init C) X ~ init C.
Proof.
  unfold isomorphic; intros.
  exists outl, (create _).
  split; cycle 1.
  - apply equiv_initial.
  - setoid_replace (create (product (init C) X)) with (fpair (id (init C)) (create X))
      by apply equiv_initial.
    rewrite fpair_comp, equiv_product', fpair_outl, fpair_outr, !comp_id_l, comp_id_r.
    split; [easy |].
Abort.
