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

Definition full {C D : Cat} (T : Functor C D) : Type :=
    forall (A B : Ob C)
    (g : Hom (fob T A) (fob T B)), {f : Hom A B | fmap T f == g}.

Definition faithful {C D : Cat} (T : Functor C D) : Prop :=
    forall (A B : Ob C) (f g : Hom A B), fmap T f == fmap T g -> f == g.

Definition iso_dense {C D : Cat} (T : Functor C D) : Type :=
    forall (Y : Ob D), {X : Ob C & fob T X ~ Y}.

Definition embedding {C D : Cat} (T : Functor C D) : Prop :=
    faithful T /\ injective (fob T).

Theorem functor_pres_sec : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y), Sec C f -> Sec D (fmap T f).
Proof.
  destruct 1 as [g g_sec]. red. exists (fmap T g).
  rewrite <- pres_comp, <- pres_id. f_equiv. assumption.
Defined.

Theorem functor_pres_ret : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y), Ret C f -> Ret D (fmap T f).
Proof.
  destruct 1 as [g g_ret]. red. exists (fmap T g).
  rewrite <- pres_comp, <- pres_id. f_equiv. assumption.
Defined.

Hint Resolve functor_pres_sec functor_pres_ret.

Theorem functor_pres_iso : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y), Iso C f -> Iso D (fmap T f).
Proof. auto. Defined.

Theorem full_faithful_refl_sec : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> Sec D (fmap T f) -> Sec C f.
Proof.
  unfold full, faithful; do 6 intro; intros T_full T_faithful.
  destruct 1 as [Tg Tg_sec], (T_full Y X Tg) as [g eq]. red.
  exists g. apply T_faithful. rewrite pres_comp, pres_id, eq. auto.
Defined.

Theorem full_faithful_refl_ret : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> Ret D (fmap T f) -> Ret C f.
Proof.
  unfold full, faithful; do 6 intro; intros T_full T_faithful.
  destruct 1 as [Tg Tg_ret], (T_full Y X Tg) as [g eq]. red.
  exists g. apply T_faithful. rewrite pres_comp, pres_id, eq. auto.
Defined.

Hint Resolve full_faithful_refl_sec full_faithful_refl_ret.

Theorem full_faithful_refl_iso : forall (C D : Cat) (T : Functor C D)
    (X Y : Ob C) (f : Hom X Y),
    full T -> faithful T -> Iso D (fmap T f) -> Iso C f.
Proof.
  intros. apply iso_is_sec_ret; eauto.
Defined.

Instance FunctorComp (C D E : Cat) (T : Functor C D) (S : Functor D E)
    : Functor C E :=
{
    fob := fun A : Ob C => fob S (fob T A);
    fmap := fun (A B : Ob C) (f : Hom A B) => fmap S (fmap T f)
}.
Proof.
  (* Proper *) proper.
  (* Functor laws *) all: functor.
Defined.

Instance FunctorId (C : Cat) : Functor C C :=
{
    fob := fun A : Ob C => A;
    fmap := fun (A B : Ob C) (f : Hom A B) => f
}.
Proof.
  (* Proper *) proper.
  (* Functors laws *) all: functor.
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
  (* Equivalence *) solve_equiv.
  (* Proper *) proper. my_simpl; solve_depExtEq.
  (* Category laws *) all: cat.
Defined.