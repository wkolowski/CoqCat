Add LoadPath "/home/Zeimer/Code/Coq/Cat".

Require Import CatInstances.

(*  BIG, REALLY BIG BEWARE: the dual category instance somehow breaks
    projection definitions in Functor and FunctorAlt. *)
Instance DualHom `(C : Cat) : @CatHom Ob.
split. destruct catHom as [Hom]. exact (fun A B : Ob => Hom B A).
Defined.

Instance DualComp `(cat : Cat) : @CatComp Ob (DualHom cat).
split. intros. destruct cat, catHom, catComp. simpl in *.
exact (comp C B A X0 X).
Defined.

Instance DualId `(C : Cat) : @CatId Ob (DualHom C).
split. intros. destruct C, catHom, catId. simpl in *.
exact (id A).
Defined.

Instance Dual `(C : Cat) : @Cat Ob (DualHom C) (DualComp C) (DualId C).
split; destruct C, catHom, catComp, catId; simpl in *; cat.
Defined.