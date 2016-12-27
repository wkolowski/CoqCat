Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Old".

Require Import ProofIrrelevance.

Require Export Cat.
(*Require Export InitTerm.
Require Import BinProdCoprod.*)

Axiom fn_ext_type : forall {A B : Type} (f g : A -> B),
f = g <-> forall a : A, f a = g a.

Lemma const_fun : forall (A B : Set) (nonempty : A) (b b' : B),
    b = b' <-> (fun _ : A => b) = (fun _ : A => b').
split; intros. rewrite H; trivial.
rewrite fn_ext_type in H. apply H. assumption.
Qed.

Instance HomIso `(C : Cat) : @CatHom Ob.
split. intros. exact {f : Hom A B | Iso f}.
Defined.

Instance CompIso `(C' : Cat) : @CatComp Ob (HomIso C').
split. unfold Hom, HomIso; intros A B C f g.
destruct f as [f f_iso], g as [g g_iso].
exists (f .> g). apply iso_comp; assumption.
Defined.

Instance IdIso `(C' : Cat) : @CatId Ob (HomIso C').
split; unfold Hom, HomIso; intros. exists (id A).
apply id_is_aut.
Defined.

(*Instance CatIso `(C' : Cat) : @Cat Ob (HomIso C') (CompIso C') (IdIso C').
split; intros. unfold comp, CompIso.
Focus 2.
destruct f. simpl. Print id_left. try rewrite id_left with A B x. cat.*)



Definition slice_over `(C : Cat) (A : Ob) := forall X : Ob, Hom X A.

