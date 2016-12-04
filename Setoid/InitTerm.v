Require Export Cat.

Set Universe Polymorphism.

Definition initial {C : Cat} (I : Ob C) : Prop :=
    forall (X : Ob C), exists!! f : Hom I X, True.

Definition terminal {C : Cat} (T : Ob C) : Prop :=
    forall (X : Ob C), exists!! f : Hom X T, True.

Definition zero_object {C : Cat} (Z : Ob C) : Prop :=
    initial Z /\ terminal Z.

Class has_init (C : Cat) : Type :=
{
    init : Ob C;
    create : forall X : Ob C, Hom init X;
    is_initial : forall (X : Ob C) (f : Hom init X), f == create X
}.

Arguments init _ [has_init].
Arguments create _ [has_init] _.

Class has_term (C : Cat) : Type :=
{
    term : Ob C;
    delete : forall X : Ob C, Hom X term;
    is_terminal : forall (X : Ob C) (f : Hom X term), f == delete X
}.

Arguments term _ [has_term].
Arguments delete _ [has_term] _.

Class has_zero (C : Cat) : Type :=
{
    zero : Ob C;
    is_zero : zero_object zero
}.

Class has_zero' (C : Cat) : Type :=
{
    zero_is_initial :> has_init C;
    zero_is_terminal :> has_term C;
    initial_is_terminal : init C = term C
}.

Definition zero' (C : Cat) {has_zero0 : has_zero' C} : Ob C := init C.

Hint Unfold initial terminal zero_object.
Hint Resolve is_initial is_terminal is_zero unique_iso_is_iso.

Theorem dual_initial_terminal : forall (C : Cat) (A : Ob C),
    @initial C A <-> @terminal (Dual C) A.
Proof. split; auto. Qed.

Theorem dual_zero_self : forall (C : Cat) (A : Ob C),
    @zero_object C A <-> @zero_object (Dual C) A.
Proof.
  unfold zero_object; repeat split; intros;
  destruct H; assumption.
Qed.

Theorem initial_unique_iso : forall (C : Cat) (A B : Ob C),
    initial A -> initial B -> A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic, initial; intros.
  destruct (H B) as [f [_ Hf]], (H0 A) as [g [_ Hg]], (H A) as [idA [_ HA]],
    (H0 B) as [idB [_ HB]].
  exists f; red. split; auto. exists g; split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Qed.

Hint Resolve initial_unique_iso.

Theorem initial_iso : forall (C : Cat) (A B : Ob C),
    initial A -> initial B -> A ~ B.
Proof. auto. Defined.

Theorem terminal_unique_iso : forall (C : Cat) (A B : Ob C),
    terminal A -> terminal B -> A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic, terminal; intros.
  destruct (H B) as [f [_ Hf]], (H0 A) as [g [_ Hg]], (H A) as [idA [_ HA]],
    (H0 B) as [idB [_ HB]].
  exists g; red. split; auto. exists f; split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Qed.

Hint Resolve terminal_unique_iso.

Theorem terminal_iso : forall (C : Cat) (A B : Ob C),
    terminal A -> terminal B -> A ~ B.
Proof. auto. Qed.

Theorem zero_unique_iso : forall (C : Cat) (A B : Ob C),
    zero_object A -> zero_object B -> A ~~ B.
Proof. unfold zero_object; cat. Qed.

Hint Resolve zero_unique_iso.

Theorem zero_iso : forall (C : Cat) (A B : Ob C),
    zero_object A -> zero_object B -> A ~ B.
Proof. auto. Qed.

Theorem mor_to_init_is_ret : forall (C : Cat) (I X : Ob C) (f : Hom X I),
    initial I -> Ret f.
Proof.
  unfold initial, Ret; intros.
  destruct (H X) as (g, [_ eq1]), (H I) as (idI, [_ eq2]). exists g.
  rewrite <- (eq2 (g .> f)); try rewrite <- (eq2 (id I)); reflexivity.
Qed.

(* There was duality, but it doesn't work in Setoid/ *)
Theorem mor_to_term_is_sec : forall (C : Cat) (T X : Ob C) (f : Hom T X),
    terminal T -> Sec f.
Proof.
  unfold terminal, Sec; intros.
  destruct (H X) as (g, [_ eq1]), (H T) as (idT, [_ eq2]). exists g.
  rewrite <- (eq2 (f .> g)); try rewrite <- (eq2 (id T)); reflexivity.
Qed.