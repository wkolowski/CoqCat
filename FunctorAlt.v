Require Export Cat.
Require Import Logic.ProofIrrelevance.

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
    pres_comp : forall {A B C : ob C} (f : Hom A B) (g : Hom B C),
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

Class Functor2 `(C : Cat) `(D : Cat) : Type :=
{
    _obPart : ObPart C D;
    _morPart : MorPart C D _obPart;
    _ : Functor C D _obPart _morPart
}.

Instance IdFunctorObPart `(C : Cat) : ObPart C C.
split. exact (fun A : ob C => A).
Defined.
Instance IdFunctorMorPart `(C : Cat) : MorPart C C (IdFunctorObPart C).
split. exact (fun (A B : ob C) (f : Hom A B) => f).
Defined.
Instance IdFunctor `(C : Cat) : Functor2 C C.
split with
    (_obPart := (IdFunctorObPart C))
    (_morPart := (IdFunctorMorPart C)).
split; trivial.
Defined.

Instance FunctorCompObPart `(C : Cat) `(D : Cat) `(E : Cat)
    (T : Functor2 C D) (S : Functor2 D E) : ObPart C E.
split. destruct T as ([fobT], _a, T), S as ([fobS], _b, S).
exact (fun A : ob C => fobS (fobT A)).
Defined.
Instance FunctorCompMorPart `(C : Cat) `(D : Cat) `(E : Cat) (T : Functor2 C D)
    (S : Functor2 D E) : MorPart C E (FunctorCompObPart C D E T S).
split. intros.
destruct T as ([fobT], [fmapT], T), S as ([fobS], [fmapS], S); simpl in *.
exact (fmapS (fobT A) (fobT B) (fmapT A B X)).
Defined.

Instance FunctorComp `(C : Cat) `(D : Cat) `(E : Cat) (T : Functor2 C D)
    (S : Functor2 D E) : Functor2 C E.
split with
    (_obPart := FunctorCompObPart C D E T S)
    (_morPart := FunctorCompMorPart C D E T S).
split; intros;
destruct T as ([fobT], [fmap], T), S as ([fobS], [fmapS], S), T, S; simpl.
rewrite pres_comp0, pres_comp1. trivial.
rewrite pres_id0, pres_id1. trivial.
Defined.

Instance CAT_Hom : @CatHom BareCat.
split. intros C D. destruct C, D. exact (Functor2 inst_ inst_0).
Defined.

Instance CAT_Comp : @CatComp BareCat CAT_Hom.
split. intros C D E T S. destruct C, D, E; simpl in *.
exact (FunctorComp inst_ inst_0 inst_1 T S).
Defined.

Instance CAT_id : @CatId BareCat CAT_Hom.
split. intro C. destruct C; simpl in *. exact (IdFunctor inst_).
Defined.

Axiom functor_eq : forall `(C : Cat) `(D : Cat) (obp : ObPart C D)
    (morp : MorPart C D obp) (T : Functor C D obp morp)
    (S : Functor C D obp morp), T = S.

Instance CAT : @Cat BareCat CAT_Hom CAT_Comp CAT_id.
split; intros.
destruct A, B, C, D. destruct f, g, h. destruct _obPart0, _obPart1, _obPart2.
destruct _morPart0, _morPart1, _morPart2.
simpl; unfold FunctorComp, FunctorCompObPart, FunctorCompMorPart.
f_equal. apply proof_irrelevance.
destruct A, B, f; destruct _obPart0, _morPart0.
simpl; unfold FunctorComp, FunctorCompObPart, FunctorCompMorPart.
f_equal. apply proof_irrelevance.
destruct A, B, f; destruct _obPart0, _morPart0.
simpl; unfold FunctorComp, FunctorCompObPart, FunctorCompMorPart.
f_equal. apply proof_irrelevance.
Defined.

Print CAT.