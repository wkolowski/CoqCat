Require Export Cat.

Class Functor (C : Cat) (D : Cat) : Type :=
{
    fob : @Ob C -> @Ob D;
    fmap : forall {A B : @Ob C}, Hom A B -> Hom (fob A) (fob B);
    fmap_Proper :> forall A B : Ob,
        Proper (equiv ==> equiv) (@fmap A B);
    pres_comp : forall {A B C : @Ob C} (f : Hom A B) (g : Hom B C),
        fmap (f .> g) == fmap f .> fmap g;
    pres_id : forall A : @Ob C, fmap (id A) == id (fob A)
}.

Print fob.
Arguments fob [C] [D] _ _.

Print fob.

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
    fob := fun A : Ob => A;
    fmap := fun (A B : Ob) (f : Hom A B) => f
|};
intros; try reflexivity.
unfold Proper. red. intros. assumption.
Defined.

Instance FunctorComp (C D E : Cat) (T : Functor C D) (S : Functor D E)
    : Functor C E.
refine
{|
    fob := fun A : @Ob C => fob S (@fob C D T A);
    fmap := fun (A B : @Ob C) (f : Hom A B) =>
        (@fmap D E S (fob T A) (fob T B) (@fmap C D T A B f))
|};
destruct C, D, E, T, S; intros; simpl.
(* Proper *) unfold Proper; red. intros. rewrite H. reflexivity.
(* Comp *) simpl. rewrite pres_comp0; simpl.
  rewrite pres_comp1; simpl. reflexivity.
(* Id *) rewrite pres_id0; simpl. rewrite pres_id1; simpl.
  reflexivity.
Defined.

Definition ext_equiv {A B : Type} (f g : A -> B) : Prop :=
    forall x : A, f x = g x.

(* The term has only 93 lines, whereas in New/Functor.v, it has 1610 *)
Instance CAT : Cat.
refine
{|
    Ob := Cat;
    Hom := Functor;
    Hom_Setoid := fun C D : Cat => {| equiv := fun T S : Functor C D =>
      ext_equiv (fob T) (fob S) /\ JMeq (@fmap C D T) (@fmap C D S) |};
        (*(forall (A B : Ob) (f : Hom A B),
            (@fmap C D T A B f) == (@fmap C D S A B f)) |};*)
    comp := FunctorComp;
    id := IdFunctor
|};
functor. red. (* Focus 2. rewrite H.
(* Equiv *) split; red; intros.
  (* Refl *) split; unfold ext_equiv; reflexivity.
  (* Sym *) destruct H as [H1 H2]; split.
    unfold ext_equiv in *. intro; rewrite H1; trivial.
    rewrite H2. trivial.
  (* Trans *) destruct H as [H1 H2], H0 as [H'1 H'2].
    unfold ext_equiv in *; split; intros.
      rewrite H1, H'1. trivial.
      rewrite H2, H'2; trivial.
(* comp_Proper *) unfold Proper, respectful; intros.
  destruct H, H0. unfold FunctorComp, ext_equiv in *; simpl. split; intros.
    rewrite H, H0; reflexivity.
  inversion H2. unfold fob in *.
    unfold fmap. destruct x, y, x0, y0. 
Focus 2. intros. simpl. split; try red; reflexivity.
Focus 2. intros. simpl. split; try red; reflexivity.
Focus 2. functor. intros. simpl. split; try red; reflexivity. *)
Abort.


Definition full `(T : Functor) : Prop := forall (A B : @Ob C)
    (g : Hom (T A) (T B)), exists f : Hom A B, fmap f == g.

Definition faithful `(T : Functor) : Prop := forall (A B : @Ob C)
    (f g : Hom A B), fmap f == fmap g -> f == g.

Definition iso_dense `(T : Functor) : Prop := forall (Y : @Ob D),
    exists X : @Ob C, T X ~ Y.

(*Definition embedding `(T : Functor) : Prop :=
    faithful T /\ injective fob.*)

(*Theorem functor_pres_sec : forall `(T : Functor) (A B : @Ob C) (f : Hom A B),
    Sec f -> Sec (fmap f).
unfold Sec; intros. destruct H as (g, H). exists (fmap g).
functor_simpl'. f_equiv. admit.
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
*)
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