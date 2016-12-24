Require Export Cat.

Require Export FunctionalExtensionality.

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

Print fob.

Definition Functor_fob `(T : Functor) := fob.
Definition Functor_fmap `(T : Functor) {A B : Ob C} (f : Hom A B) := fmap f.
Coercion Functor_fob : Functor >-> Funclass.
Coercion Functor_fmap : Functor >-> Funclass.

Ltac functor_rw := rewrite pres_comp || rewrite pres_id.
Ltac functor_rw' := rewrite <- pres_comp || rewrite <- pres_id.
Ltac functor_simpl := repeat functor_rw.
Ltac functor_simpl' := repeat functor_rw'.
Ltac functor := repeat (split || intros || functor_simpl || cat).

Definition full {C D : Cat} (T : Functor C D) : Prop :=
    forall (A B : Ob C)
    (g : Hom (T A) (T B)), exists f : Hom A B, fmap f == g.

Definition faithful {C D : Cat} (T : Functor C D) : Prop :=
    forall (A B : Ob C) (f g : Hom A B), fmap f == fmap g -> f == g.

Definition iso_dense {C D : Cat} (T : Functor C D) : Prop :=
    forall (Y : Ob D), exists X : Ob C, T X ~ Y.

Definition embedding `(T : Functor) : Prop :=
    faithful T /\ injective fob.

Theorem functor_pres_sec : forall `(T : Functor) (A B : Ob C) (f : Hom A B),
    Sec f -> Sec (fmap f).
Proof.
  unfold Sec; intros. destruct H as (g, H). exists (fmap g).
  functor_simpl'. f_equiv. assumption.
Qed.

Theorem functor_pres_ret : forall `(T : Functor) (A B : Ob C) (f : Hom A B),
    Ret f -> Ret (fmap f).
Proof.
  unfold Ret; intros. destruct H as (g, H'). exists (fmap g).
  functor_simpl'. f_equiv. assumption.
Restart.
  unfold Ret; cat. exists (fmap x). rewrite <- pres_comp. rewrite H.
  functor.
Qed.

Theorem functor_pres_iso : forall `(T : Functor) (A B : Ob C) (f : Hom A B),
    Iso f -> Iso (fmap f).
Proof.
  intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H.
  destruct H as (H_sec, H_ret). split.
    apply functor_pres_sec; assumption.
    apply functor_pres_ret; assumption.
Qed.

Theorem full_faithful_refl_sec : forall `(T : Functor) (A B : Ob C)
    (f : Hom A B), full T -> faithful T -> Sec (fmap f) -> Sec f.
Proof.
  unfold full, faithful, Sec; intros.
  rename H into T_full, H0 into T_faithful.
  destruct H1 as (g, H).
  destruct (T_full B A g) as [g' eq].
  exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
  rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_ret : forall `(T : Functor) (A B : Ob C)
    (f : Hom A B), full T -> faithful T -> Ret (fmap f) -> Ret f.
Proof.
  unfold full, faithful, Sec; intros.
  rename H into T_full, H0 into T_faithful.
  destruct H1 as (g, H). destruct (T_full B A g) as [g' eq].
  exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
  rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_iso : forall `(T : Functor) (A B : Ob C)
    (f : Hom A B), full T -> faithful T -> Iso (fmap f) -> Iso f.
Proof.
  intros. rewrite iso_iff_sec_ret in *.
  destruct H1 as (H_sec, H_ret). split.
  apply full_faithful_refl_sec with T; assumption.
  apply full_faithful_refl_ret with T; assumption.
Qed.

Instance FunctorComp (C D E : Cat) (T : Functor C D) (S : Functor D E)
    : Functor C E :=
{
    fob := fun A : Ob C => fob S (fob T A); (*fob S (@fob C D T A);*)
    fmap := fun (A B : Ob C) (f : Hom A B) =>
        S (T f) (*(fmap S (T A) (T B) (@fmap C D T A B f))*)
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

(* The term has only 93 lines, whereas in New/Functor.v, it has 1610 *)
Instance CAT : Cat :=
{
    Ob := Cat;
    Hom := Functor;
    HomSetoid := fun C D : Cat =>
      {| equiv := fun T S : Functor C D =>
        (forall X : Ob C, T X = S X) /\
        forall (A B : Ob C) (f : Hom A B),
          JMeq (@fmap C D T A B f) (@fmap C D S A B f) |};
        (*(forall (A B : Ob) (f : Hom A B),
            (@fmap C D T A B f) == (@fmap C D S A B f)) |};*)
    comp := FunctorComp;
    id := FunctorId
}.
Proof.
  all: functor. rewrite H, H0. auto. rewrite H2, H1.
  unfold equiv, ext_equiv in *. destruct H, H0.
    intros. simpl. rewrite H, H0. reflexivity.
  unfold equiv, ext_equiv in *. destruct H, H0.
    simpl in *. rewrite H2.
Abort. *)
