Require Export Cat.

Require Export Equivalences.

Class Functor (C : Cat) (D : Cat) : Type :=
{
    fob : Ob C -> Ob D;
    fmap : forall {A B : Ob C}, Hom A B -> Hom (fob A) (fob B);
    fmap_Proper :> forall A B : Ob C,
        Proper (equiv ==> equiv) (@fmap A B);
    pres_comp : forall {A B C : Ob C} (f : Hom A B) (g : Hom B C),
        fmap (f .> g) == fmap f .> fmap g;
    pres_id : forall A : Ob C, fmap (id A) == id (fob A)
}.

Arguments fob [C] [D] _ _.
Arguments fmap [C] [D] _ [A] [B] _.

Ltac functor_rw := rewrite pres_comp || rewrite pres_id.
Ltac functor_rw' := rewrite <- pres_comp || rewrite <- pres_id.
Ltac functor_simpl := repeat functor_rw.
Ltac functor_simpl' := repeat functor_rw'.
Ltac functor := repeat (split || intros || functor_simpl || cat).

Definition full {C D : Cat} (T : Functor C D) : Prop :=
    forall (A B : Ob C)
    (g : Hom (fob T A) (fob T B)), exists f : Hom A B, fmap T f == g.

Definition faithful {C D : Cat} (T : Functor C D) : Prop :=
    forall (A B : Ob C) (f g : Hom A B), fmap T f == fmap T g -> f == g.

Definition iso_dense {C D : Cat} (T : Functor C D) : Prop :=
    forall (Y : Ob D), exists X : Ob C, fob T X ~ Y.

Definition embedding `(T : Functor) : Prop :=
    faithful T /\ injective (fob T).

Theorem functor_pres_sec : forall `(T : Functor) (A B : Ob C) (f : Hom A B),
    Sec f -> Sec (fmap T f).
Proof.
  unfold Sec; intros. destruct H as (g, H). exists (fmap T g).
  functor_simpl'. f_equiv. assumption.
Qed.

Theorem functor_pres_ret : forall `(T : Functor) (A B : Ob C) (f : Hom A B),
    Ret f -> Ret (fmap T f).
Proof.
  unfold Ret; intros. destruct H as (g, H'). exists (fmap T g).
  functor_simpl'. f_equiv. assumption.
Restart.
  unfold Ret; cat. exists (fmap T x). rewrite <- pres_comp. rewrite H.
  functor.
Qed.

Theorem functor_pres_iso : forall `(T : Functor) (A B : Ob C) (f : Hom A B),
    Iso f -> Iso (fmap T f).
Proof.
  intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H.
  destruct H as (H_sec, H_ret). split.
    apply functor_pres_sec; assumption.
    apply functor_pres_ret; assumption.
Qed.

Theorem full_faithful_refl_sec : forall `(T : Functor) (A B : Ob C)
    (f : Hom A B), full T -> faithful T -> Sec (fmap T f) -> Sec f.
Proof.
  unfold full, faithful, Sec; intros.
  rename H into T_full, H0 into T_faithful.
  destruct H1 as (g, H).
  destruct (T_full B A g) as [g' eq].
  exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
  rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_ret : forall `(T : Functor) (A B : Ob C)
    (f : Hom A B), full T -> faithful T -> Ret (fmap T f) -> Ret f.
Proof.
  unfold full, faithful, Sec; intros.
  rename H into T_full, H0 into T_faithful.
  destruct H1 as (g, H). destruct (T_full B A g) as [g' eq].
  exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
  rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_iso : forall `(T : Functor) (A B : Ob C)
    (f : Hom A B), full T -> faithful T -> Iso (fmap T f) -> Iso f.
Proof.
  intros. rewrite iso_iff_sec_ret in *.
  destruct H1 as (H_sec, H_ret). split.
  apply full_faithful_refl_sec with T; assumption.
  apply full_faithful_refl_ret with T; assumption.
Qed.

Instance FunctorComp (C D E : Cat) (T : Functor C D) (S : Functor D E)
    : Functor C E :=
{
    fob := fun A : Ob C => fob S (fob T A);
    fmap := fun (A B : Ob C) (f : Hom A B) => fmap S (fmap T f)
}.
Proof.
  all: functor.
  (* Proper *) unfold Proper; red. intros. rewrite H. reflexivity.
Defined.

Instance FunctorId (C : Cat) : Functor C C :=
{
    fob := fun A : Ob C => A;
    fmap := fun (A B : Ob C) (f : Hom A B) => f
}.
Proof.
  all: functor. repeat red. cat.
Defined.

Instance CAT : Cat :=
{
    Ob := Cat;
    Hom := Functor;
    HomSetoid := fun C D : Cat =>
      {| equiv := fun T S : Functor C D =>
        depExtEq (fob T) (fob S) /\ depExtEq (fmap T) (fmap S) |};
    comp := FunctorComp;
    id := FunctorId
}.
Proof.
  (* Equivalence *) repeat (red || split); try destruct H; auto;
  try destruct H0; auto; eapply depExtEq_trans; eauto.
  (* Proper *) repeat red; simpl; intros. destruct H, H0. split.
    solve_depExtEq.
    destruct x, y, x0, y0; simpl in *. solve_depExtEq.
  (* Category laws *) all: cat.
Defined.