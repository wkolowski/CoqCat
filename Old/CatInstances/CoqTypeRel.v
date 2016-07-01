Add LoadPath "/home/Zeimer/Code/Coq/Cat".

Require Import CatInstances.
Require Import ProofIrrelevance.

Axiom prop_ext : forall (A B : Prop), A = B <-> (A <-> B).

Instance RelHom : @CatHom Type.
split; intros. exact (A -> B -> Prop).
Defined.

Instance RelComp : @CatComp Type RelHom.
split; unfold Hom, RelHom; intros A B C R S a c.
exact (exists b : B, R a b /\ S b c).
Defined.

Instance RelId : @CatId Type RelHom.
split. intro. exact eq.
Defined.

Instance Rel : @Cat Type RelHom RelComp RelId.
split; unfold Hom, RelHom, comp, RelComp.
intros A B C D R S T.
rewrite fn_ext_type; intro a; rewrite fn_ext_type; intro d.
rewrite prop_ext. split; intro.
destruct H as [c [[b [eq1 eq2]] eq3]].
exists b. split; try assumption.
exists c. split; assumption.
destruct H as [b [eq1 [c [eq2 eq3]]]].
exists c; split. exists b; split; assumption. assumption.
intros A B R. rewrite fn_ext_type. intro. rewrite fn_ext_type. intro b.
rewrite prop_ext; split; intros.
simpl in H. destruct H as [a' [eq p]].
rewrite eq; assumption.
exists a; split; [reflexivity | assumption].
intros A B R. rewrite fn_ext_type. intro. rewrite fn_ext_type. intro b.
rewrite prop_ext; split; intros.
simpl in H. destruct H as [a' [p eq]].
rewrite <- eq; assumption.
exists b; split; [assumption | reflexivity].
Qed.
