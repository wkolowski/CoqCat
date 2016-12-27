Require Import Logic.ProofIrrelevance.

Require Export Cat.
(*Require Import BinProdCoprod.*)

Class Functor `(C : Cat) `(D : Cat) (fob : ob C -> ob D)
    `(fhom : forall {A B : ob C}, Hom A B -> Hom (fob A) (fob B)) : Type :=
{
    pres_comp : forall {A B C : ob C} (f : Hom A B) (g : Hom B C),
        fhom (f .> g) = fhom f .> fhom g;
    pres_id : forall A : ob C, fhom (id A) = id (fob A)
}.

Ltac functor_rw := rewrite pres_comp || rewrite pres_id.
Ltac functor_rw' := rewrite <- pres_comp || rewrite <- pres_id.
Ltac functor_simpl := repeat functor_rw.
Ltac functor_simpl' := repeat functor_rw'.
Ltac functor := repeat (split || intros || functor_simpl || cat).

Theorem functor_pres_sec : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    Sec f -> Sec (fhom A B f).
unfold Sec; intros.
destruct H as (g, H'). exists (@fhom B A g).
rewrite <- pres_comp. rewrite <- pres_id. f_equal. assumption.
Qed.

Theorem functor_pres_ret : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    Ret f -> Ret (@fhom A B f).
unfold Ret; intros. destruct H as (g, H'). exists (@fhom B A g).
rewrite <- pres_comp, <- pres_id. apply f_equal; assumption.
Qed.

Theorem functor_pres_iso : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    Iso f -> Iso (@fhom A B f).
intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H.
destruct H as (H_sec, H_ret).
split. apply functor_pres_sec; assumption.
apply functor_pres_ret; assumption.
Qed.

Definition full `(T : Functor) : Prop := forall (A B : ob C)
    (g : Hom (fob A) (fob B)), exists f : Hom A B, @fhom A B f = g.

Definition faithful `(T : Functor) : Prop := forall (A B : ob C)
    (f g : Hom A B), @fhom A B f = @fhom A B g -> f = g.

Definition iso_dense `(T : Functor) : Prop := forall (Y : ob D),
    exists X : ob C, fob X ~ Y.

(*Definition embedding `(T : Functor) : Prop :=
    faithful T /\ injective fob.*)

Theorem full_faithful_refl_sec : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    full T -> faithful T -> Sec (@fhom A B f) -> Sec f.
unfold full, faithful, Sec; intros. rename H into T_full, H0 into T_faithful.
destruct H1 as (g, H).
destruct (T_full B A g) as [g' eq].
exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_ret : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    full T -> faithful T -> Ret (@fhom A B f) -> Ret f.
unfold full, faithful, Sec; intros. rename H into T_full, H0 into T_faithful.
destruct H1 as (g, H). destruct (T_full B A g) as [g' eq].
exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_iso : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    full T -> faithful T -> Iso (@fhom A B f) -> Iso f.
intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H1.
destruct H1 as (H_sec, H_ret). split.
apply full_faithful_refl_sec with T; assumption.
apply full_faithful_refl_ret with T; assumption.
Qed.

Class Functor2 `(C : Cat) `(D : Cat) : Type :=
{
    fob : ob C -> ob D;
    fmap : forall (A B : ob C), Hom A B -> Hom (fob A) (fob B);
    _ : Functor C D fob fmap
}.

Print Functor2.

Definition Functor2_proj `(T : Functor2) := fmap.
Coercion Functor2_proj : Functor2 >-> Funclass.

Instance IdFunctor `(C : Cat) : Functor2 C C.
split with
    (fob := fun A : ob C => A)
    (fmap := fun (A B : ob C) (f : Hom A B) => f).
functor.
Defined.

Print IdFunctor.

Instance FunctorComp `(C : Cat) `(D : Cat) `(E : Cat) (T : Functor2 C D)
    (S : Functor2 D E) : Functor2 C E.
split with
    (fob := fun A : ob C => fob (fob A))
    (fmap := fun (A B : ob C) (f : Hom A B) => S (fob A) (fob B) (T A B f)).
destruct T, S. functor. 
Defined.

Print FunctorComp.

Instance CAT_Hom : @CatHom Cat'.
split. intros C D. destruct C, D. exact (Functor2 inst_ inst_0).
Defined.

Instance CAT_Comp : @CatComp Cat' CAT_Hom.
split. intros C D E T S. destruct C, D, E; simpl in *.
exact (FunctorComp inst_ inst_0 inst_1 T S).
Defined.

Instance CAT_id : @CatId Cat' CAT_Hom.
split. destruct 0; simpl. exact (IdFunctor inst_).
Defined.

Instance CAT : @Cat Cat' CAT_Hom CAT_Comp CAT_id.
split; intros.
destruct A, B, C, D, f, g, h. simpl. unfold FunctorComp.
f_equal. apply proof_irrelevance.
destruct A, B, f; simpl; unfold FunctorComp.
f_equal. apply proof_irrelevance.
destruct A, B, f; simpl; unfold FunctorComp.
f_equal. apply proof_irrelevance.
Defined.

Print CAT.