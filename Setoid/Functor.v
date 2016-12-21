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

Definition Functor_fob `(T : Functor) := fob.
Definition Functor_fmap `(T : Functor) {A B : Ob C} (f : Hom A B) := fmap f.
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
intros; try reflexivity.
unfold Proper. red. intros. assumption.
Defined.

Instance FunctorComp (C D E : Cat) (T : Functor C D) (S : Functor D E)
    : Functor C E.
refine
{|
    fob := fun A : Ob C => S (T A); (*fob S (@fob C D T A);*)
    fmap := fun (A B : Ob C) (f : Hom A B) =>
        fmap (fmap f) (*(fmap S (T A) (T B) (@fmap C D T A B f))*)
|};
functor.
(* Proper *) unfold Proper; red. intros. rewrite H. reflexivity.
(*(* Comp *) simpl. rewrite pres_comp0; simpl.
  rewrite pres_comp1; simpl. reflexivity.
(* Id *) rewrite pres_id0; simpl. rewrite pres_id1; simpl.
  reflexivity.*)
Defined.

Definition ext_equiv {A B : Type} (f g : A -> B) : Prop :=
    forall x : A, f x = g x.

(* The term has only 93 lines, whereas in New/Functor.v, it has 1610 *)
(*Instance CAT : Cat.
refine
{|
    Ob := Cat;
    Hom := Functor;
    Hom_Setoid := fun C D : Cat => {| equiv := fun T S : Functor C D =>
      ext_equiv (fob T) (fob S) /\ forall (A B : Ob C) (f : Hom A B),
      JMeq (@fmap C D T A B f) (@fmap C D S A B f) |};
        (*(forall (A B : Ob) (f : Hom A B),
            (@fmap C D T A B f) == (@fmap C D S A B f)) |};*)
    comp := FunctorComp;
    id := IdFunctor
|};
functor.
  unfold equiv, ext_equiv in *. destruct H, H0.
    intros. simpl. rewrite H, H0. reflexivity.
  unfold equiv, ext_equiv in *. destruct H, H0.
    simpl in *. rewrite H2.
Abort.

Definition full {C D : Cat} (T : Functor C D) : Prop := forall (A B : Ob C)
    (g : Hom (T C D T A) (T C D T B)), exists f : Hom A B, fmap f == g.

Definition faithful `(T : Functor) : Prop := forall (A B : Ob C)
    (f g : Hom A B), fmap f == fmap g -> f == g.

Definition iso_dense `(T : Functor) : Prop := forall (Y : Ob D),
    exists X : Ob C, T X ~ Y.*)

(*Definition embedding `(T : Functor) : Prop :=
    faithful T /\ injective fob.*)

(*Theorem functor_pres_sec : forall `(T : Functor) (A B : Ob C) (f : Hom A B),
    Sec f -> Sec (fmap f).
unfold Sec; intros. destruct H as (g, H). exists (fmap g).
functor_simpl'. f_equiv. admit.
Qed.

Theorem functor_pres_ret : forall `(T : Functor) (A B : Ob C) (f : Hom A B),
    Ret f -> Ret (fmap f).
unfold Ret; intros. destruct H as (g, H'). exists (fmap g).
functor_simpl'. f_equal; assumption.
Qed.

Theorem functor_pres_iso : forall `(T : Functor) (A B : Ob C) (f : Hom A B),
    Iso f -> Iso (fmap f).
intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H.
destruct H as (H_sec, H_ret).
split. apply functor_pres_sec; assumption.
apply functor_pres_ret; assumption.
Qed.
*)

(* NOWO SKASOWANE: 25.11.2016 ======================================= *)

(*Theorem full_faithful_refl_sec : forall `(T : Functor) (A B : Ob C)
    (f : Hom A B), full T -> faithful T -> Sec (fmap f) -> Sec f.
unfold full, faithful, Sec; intros. rename H into T_full, H0 into T_faithful.
destruct H1 as (g, H).
destruct (T_full B A g) as [g' eq].
exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_ret : forall `(T : Functor) (A B : Ob C)
    (f : Hom A B), full T -> faithful T -> Ret (fmap f) -> Ret f.
unfold full, faithful, Sec; intros. rename H into T_full, H0 into T_faithful.
destruct H1 as (g, H). destruct (T_full B A g) as [g' eq].
exists g'. rewrite <- eq in H. rewrite <- pres_comp in H.
rewrite <- pres_id in H. apply T_faithful in H. assumption.
Qed.

Theorem full_faithful_refl_iso : forall `(T : Functor) (A B : Ob C)
    (f : Hom A B), full T -> faithful T -> Iso (fmap f) -> Iso f.
intros. rewrite iso_iff_sec_ret. rewrite iso_iff_sec_ret in H1.
destruct H1 as (H_sec, H_ret). split.
apply full_faithful_refl_sec with T; assumption.
apply full_faithful_refl_ret with T; assumption.
Qed.*)