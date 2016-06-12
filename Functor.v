Require Export Cat.

Class Functor `(C : Cat) `(D : Cat) (fob : ob C -> ob D)
    `(fhom : forall {A B : ob C}, Hom A B -> Hom (fob A) (fob B)) : Type :=
{
    pres_comp : forall {A B C : ob C} (f : Hom A B) (g : Hom B C),
        fhom (f .> g) = fhom f .> fhom g;
    pres_id : forall A : ob C, fhom (id A) = id (fob A)
}.

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

Definition embedding `(T : Functor) : Prop :=
    faithful T /\ injective fob.

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

(*Theorem comp_full : forall `(C : Cat) `(D : Cat) `(E : Cat)
    (fob1 : ob C -> ob D) (fob2 : ob D -> ob E)
    (fhom1 : forall A B : ob C, Hom A B -> Hom (fob1 A) (fob1 B))
    (fhom2 : forall A B : ob D, Hom A B -> Hom (fob2 A) (fob2 B))
    (T1 : Functor C D fob1 fhom1) (T2 : Functor D E fob2 fhom2)
    (TComp : Functor C E (fun A : ob C => fob2 (fob1 A))
        (forall A B : ob C, Hom A B -> Hom ),
    full T1 -> full T2 -> full TComp.*)