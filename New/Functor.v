Require Export Cat.

Set Universe Polymorphism.

Class Functor (C : Cat) (D : Cat) : Type :=
{
    fob : @Ob C -> @Ob D;
    fmap : forall {A B : @Ob C}, Hom A B -> Hom (fob A) (fob B);
    pres_comp : forall {A B C : @Ob C} (f : Hom A B) (g : Hom B C),
        fmap (f .> g) = fmap f .> fmap g;
    pres_id : forall A : @Ob C, fmap (id A) = id (fob A)
}.

(*Arguments fob [C] [D] _ _.
Print fob.*)

Definition Functor_fob `(T : Functor) := fob.
Definition Functor_fmap `(T : Functor) {A B : @Ob C} (f : Hom A B) := fmap f.
Coercion Functor_fob : Functor >-> Funclass.
Coercion Functor_fmap : Functor >-> Funclass.

Ltac functor_rw := rewrite pres_comp || rewrite pres_id.
Ltac functor_rw' := rewrite <- pres_comp || rewrite <- pres_id.
Ltac functor_simpl := repeat functor_rw.
Ltac functor_simpl' := repeat functor_rw'.
Ltac functor := repeat (split || intros || functor_simpl || cat).

Instance IdFunctor (C : Cat) : Functor C C.
refine
{|
    fob := fun A : Ob C => A;
    fmap := fun (A B : Ob C) (f : Hom A B) => f
|};
trivial.
Defined.

Instance FunctorComp (C D E : Cat) (T : Functor C D) (S : Functor D E) : Functor C E.
refine
{|
    fob := fun A : Ob C => S (T A);
    fmap := fun (A B : @Ob C) (f : Hom A B) => fmap (fmap f)
|};
functor.
Defined.

(*Inductive locally_small : Cat -> Prop :=
    | small_c : forall (Ob : Type) (Hom : forall A B : Ob, Set)
        (comp : forall A B C : Ob, Hom A B -> Hom B C -> Hom A C)
        (id : forall A : Ob, Hom A A), locally_small (Build_Cat Ob Hom comp id _ _ _).
*)
Instance CAT : Cat.
refine
{|
    Ob := Cat;
    Hom := Functor;
    comp := FunctorComp;
    id := IdFunctor
|};
intros; [destruct f, g, h | destruct f | destruct f];
unfold FunctorComp; simpl; f_equal; apply proof_irrelevance.
Defined.

Definition full `(T : Functor) : Prop := forall (A B : @Ob C)
    (g : Hom (T A) (T B)), exists f : Hom A B, fmap f = g.

Definition faithful `(T : Functor) : Prop := forall (A B : @Ob C)
    (f g : Hom A B), fmap f = fmap g -> f = g.

Definition iso_dense `(T : Functor) : Prop := forall (Y : @Ob D),
    exists X : @Ob C, T X ~ Y.

(*Definition embedding `(T : Functor) : Prop :=
    faithful T /\ injective fob.*)

Theorem functor_pres_sec : forall `(T : Functor) (A B : @Ob C) (f : Hom A B),
    Sec f -> Sec (fmap f).
unfold Sec; intros. destruct H as (g, H'). exists (fmap g).
functor_simpl'. f_equal. assumption.
Qed.

Theorem functor_pres_ret : forall `(T : Functor) (A B : @Ob C) (f : Hom A B),
    Ret f -> Ret (fmap f).
unfold Ret; intros. destruct H as (g, H'). exists (fmap g).
functor_simpl'. f_equal; assumption.
Qed.

Theorem functor_pres_iso : forall `(T : Functor) (A B : @Ob C) (f : Hom A B),
    Iso f -> Iso (fmap f).
intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H.
destruct H as (H_sec, H_ret).
split. apply functor_pres_sec; assumption.
apply functor_pres_ret; assumption.
Qed.

Theorem full_faithful_refl_sec : forall `(T : Functor) (A B : @Ob C)
    (f : Hom A B), full T -> faithful T -> Sec (fmap f) -> Sec f.
unfold full, faithful, Sec; intros. rename H into T_full, H0 into T_faithful.
destruct H1 as (g, H).
destruct (T_full B A g) as [g' eq].
exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_ret : forall `(T : Functor) (A B : @Ob C)
    (f : Hom A B), full T -> faithful T -> Ret (fmap f) -> Ret f.
unfold full, faithful, Sec; intros. rename H into T_full, H0 into T_faithful.
destruct H1 as (g, H). destruct (T_full B A g) as [g' eq].
exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_iso : forall `(T : Functor) (A B : @Ob C)
    (f : Hom A B), full T -> faithful T -> Iso (fmap f) -> Iso f.
intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H1.
destruct H1 as (H_sec, H_ret). split.
apply full_faithful_refl_sec with T; assumption.
apply full_faithful_refl_ret with T; assumption.
Qed.