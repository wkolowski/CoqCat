Require Export Cat.

Class ObPart `(C : Cat) `(D : Cat) : Type :=
{
    fob : ob C -> ob D
}.
Definition ObPart_coercion `(_ : ObPart) := fob.
Coercion ObPart_coercion : ObPart >-> Funclass.

Class MorPart `(C : Cat) `(D : Cat) (fob : ObPart C D) : Type :=
{
    fmap : forall {A B : ob C}, Hom A B -> Hom (fob A) (fob B)
}.

Class Functor `(C : Cat) `(D : Cat) (fobInst : ObPart C D)
    (fhomInst : MorPart C D fobInst) : Type :=
{
    pres_comp : forall (A B C : ob C) (f : Hom A B) (g : Hom B C),
        fmap (f .> g) = fmap f .> fmap g;
    pres_id : forall A : ob C, fmap (id A) = id (fob A)
}.
Definition fn_fhom3 `(T : Functor) {A B : ob C} (f : Hom A B) := fmap f.
Coercion fn_fhom3 : Functor >-> Funclass.

Theorem functor_pres_sec : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    Sec f -> Sec (fmap f).
unfold Sec; intros.
destruct H as (g, H'). exists (fmap g).
rewrite <- pres_comp. rewrite <- pres_id. f_equal. assumption.
Qed.

Theorem functor_pres_ret : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    Ret f -> Ret (fmap f).
unfold Ret; intros. destruct H as (g, H'). exists (fmap g).
rewrite <- pres_comp, <- pres_id. apply f_equal; assumption.
Qed.

Theorem functor_pres_iso : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    Iso f -> Iso (fmap f).
intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H.
destruct H as (H_sec, H_ret).
split. apply functor_pres_sec; assumption.
apply functor_pres_ret; assumption.
Qed.

Definition full `(T : Functor) : Prop := forall (A B : ob C)
    (g : Hom (fob A) (fob B)), exists f : Hom A B, fmap f = g.

Definition faithful `(T : Functor) : Prop := forall (A B : ob C)
    (f g : Hom A B), fmap f = fmap g -> f = g.

Definition iso_dense `(T : Functor) : Prop := forall (Y : ob D),
    exists X : ob C, fob X ~ Y.

(*Definition embedding `(T : Functor) : Prop :=
    faithful T /\ injective fob.*)

Theorem full_faithful_refl_sec : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    full T -> faithful T -> Sec (fmap f) -> Sec f.
unfold full, faithful, Sec; intros. rename H into T_full, H0 into T_faithful.
destruct H1 as (g, H).
destruct (T_full B A g) as [g' eq].
exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_ret : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    full T -> faithful T -> Ret (fmap f) -> Ret f.
unfold full, faithful, Sec; intros. rename H into T_full, H0 into T_faithful.
destruct H1 as (g, H). destruct (T_full B A g) as [g' eq].
exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_iso : forall `(T : Functor) (A B : ob C) (f : Hom A B),
    full T -> faithful T -> Iso (fmap f) -> Iso f.
intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H1.
destruct H1 as (H_sec, H_ret). split.
apply full_faithful_refl_sec with T; assumption.
apply full_faithful_refl_ret with T; assumption.
Qed.