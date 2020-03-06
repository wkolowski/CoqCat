Require Import Cat.Cat.

Set Implicit Arguments.

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

Definition embedding {C D : Cat} (T : Functor C D) : Prop :=
    faithful T /\ injective (fob T).

Hint Unfold full faithful iso_dense embedding.

Theorem functor_pres_sec : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y), Sec f -> Sec (fmap T f).
Proof.
  unfold Sec; intros. destruct H as (g, H). exists (fmap T g).
  functor_simpl'. f_equiv. assumption.
Defined.

Theorem functor_pres_ret : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y), Ret f -> Ret (fmap T f).
Proof.
  unfold Ret; intros. destruct H as (g, H'). exists (fmap T g).
  functor_simpl'. f_equiv. assumption.
Restart.
  unfold Ret; cat. exists (fmap T x). rewrite <- pres_comp, e.
  functor.
Defined.

Hint Resolve functor_pres_sec functor_pres_ret.

Theorem functor_pres_iso : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y), Iso f -> Iso (fmap T f).
Proof. intros. rewrite iso_iff_sec_ret in *. cat. Defined.

Theorem full_faithful_refl_sec : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> Sec (fmap T f) -> Sec f.
Proof.
  unfold full, faithful; do 6 intro; intros T_full T_faithful.
  destruct 1 as [Tg Tg_sec], (T_full Y X Tg) as [g eq]. red.
  exists g. apply T_faithful. rewrite pres_comp, pres_id, eq. auto.
Defined.

Theorem full_faithful_refl_ret : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> Ret (fmap T f) -> Ret f.
Proof.
  unfold full, faithful; do 6 intro; intros T_full T_faithful.
  destruct 1 as [Tg Tg_ret], (T_full Y X Tg) as [g eq]. red.
  exists g. apply T_faithful. rewrite pres_comp, pres_id, eq. auto.
Defined.

Hint Resolve full_faithful_refl_sec full_faithful_refl_ret.

Theorem full_faithful_refl_iso : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> Iso (fmap T f) -> Iso f.
Proof.
  intros. rewrite iso_iff_sec_ret in *. destruct H1. split.
    eapply full_faithful_refl_sec; auto.
    eapply full_faithful_refl_ret; auto.
    (* TODO : cat should work here *)
Defined.

#[refine]
Instance FunctorComp {C D E : Cat} (T : Functor C D) (S : Functor D E)
    : Functor C E :=
{
    fob := fun A : Ob C => fob S (fob T A);
    fmap := fun (X Y : Ob C) (f : Hom X Y) => fmap S (fmap T f)
}.
Proof.
  (* Proper *) proper.
  (* Functor laws *) all: functor.
Defined.

#[refine]
Instance FunctorId (C : Cat) : Functor C C :=
{
    fob := fun A : Ob C => A;
    fmap := fun (X Y : Ob C) (f : Hom X Y) => f
}.
Proof.
  (* Proper *) proper.
  (* Functors laws *) all: functor.
Defined.

#[refine]
Instance CAT : Cat :=
{
    Ob := Cat;
    Hom := Functor;
    HomSetoid := fun C D : Cat =>
      {| equiv := fun T S : Functor C D =>
        depExtEq (fob T) (fob S) /\ depExtEq (fmap T) (fmap S) |};
    comp := @FunctorComp;
    id := FunctorId
}.
Proof.
  (* Equivalence *) solve_equiv.
  (* Proper *) proper. my_simpl; solve_depExtEq.
  (* Category laws *) all: cat.
Defined.

#[refine]
Instance ConstFunctor {D : Cat} (X : Ob D) (C : Cat)
    : Functor C D :=
{
    fob := fun _ => X;
    fmap := fun _ _ _ => id X
}.
Proof. proper. all: functor. Defined.