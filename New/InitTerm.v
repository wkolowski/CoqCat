Require Export Cat.

Definition initial {C : Cat} (I : Ob) : Prop :=
    forall (X : Ob), exists! f : Hom I X, True.

Definition terminal {C : Cat} (T : Ob) : Prop :=
    forall (X : Ob), exists! f : Hom X T, True.

Definition zero_object {C : Cat} (Z : Ob) : Prop :=
    initial Z /\ terminal Z.

Definition has_initial_object (C : Cat) : Prop :=
    exists I : Ob, initial I.

Definition has_terminal_object (C : Cat) : Prop :=
    exists T : Ob, terminal T.

Definition has_zero_object (C : Cat) : Prop :=
    exists Z : Ob, zero_object Z.

Theorem dual_initial_terminal : forall (C : Cat) (A : Ob),
    @initial C A <-> @terminal (Dual C) A.
unfold initial, terminal; split; intros.
unfold Hom, Dual. apply H.
unfold Hom, Dual in H. apply H.
Qed.

Theorem dual_zero_self : forall (C : Cat) (A : Ob),
    @zero_object C A <-> @zero_object (Dual C) A.
unfold zero_object; repeat split; intros;
destruct H; assumption.
Qed.

Theorem initial_ob_iso_unique : forall (C : Cat) (A B : Ob),
    initial A -> initial B -> A ~ B.
unfold initial, isomorphic; intros.
destruct (H A) as (id1, [_ eq1]), (H0 B) as (id2, [_ eq2]),
(H B) as (f, _), (H0 A) as (g, _); clear H H0.
exists f; unfold Iso; exists g; split.
rewrite <- (eq1 (f .> g)); [rewrite <- (eq1 (id A)); trivial | trivial].
rewrite <- (eq2 (g .> f)); [rewrite <- (eq2 (id B)); trivial | trivial].
Qed.

Theorem initial_ob_uniquely_isomorphic : forall (C : Cat) (A B : Ob),
    initial A -> initial B -> A ~~ B.
unfold uniquely_isomorphic; intros.
assert (A ~ B). apply initial_ob_iso_unique; assumption.
destruct H1 as [f [g [eq1 eq2]]].
exists f. split. unfold Iso; exists g; split; assumption.
intros f' iso_f'. unfold initial in *.
destruct (H B) as []. destruct H1.
assert (x = f). apply H2. trivial.
rewrite <- H3. apply H2. trivial.
Qed.

Theorem terminal_ob_iso_unique : forall (C : Cat) (A B : Ob),
    terminal A -> terminal B -> A ~ B.
unfold terminal, isomorphic; intros.
destruct (H A) as (id1, [_ eq1]), (H0 B) as (id2, [_ eq2]),
(H B) as (f, _), (H0 A) as (g, _); clear H H0.
exists g; unfold Iso; exists f; split.
rewrite <- (eq1 (g .> f)); [rewrite <- (eq1 (id A)); trivial | trivial].
rewrite <- (eq2 (f .> g)); [rewrite <- (eq2 (id B)); trivial | trivial].
Qed.

Theorem terminal_ob_uniquely_isomorphic : forall (C : Cat) (A B : Ob),
    terminal A -> terminal B -> A ~~ B.
(*intro C. rewrite <- (dual_involution C). intros.
rewrite <- (dual_initial_terminal (Dual C)) in *.
unfold uniquely_isomorphic. unfold initial in H0.
unfold Hom in H0. unfold Dual in H0.
specialize (H0 A).
*)
unfold uniquely_isomorphic; intros.
assert (A ~ B). apply terminal_ob_iso_unique; assumption.
destruct H1 as [f [g [eq1 eq2]]].
exists f. split. unfold Iso; exists g; split; assumption.
intros f' iso_f'. unfold terminal in *.
destruct (H0 A) as []. destruct H1.
assert (x = f). apply H2. trivial.
rewrite <- H3. apply H2. trivial.
Qed.

Theorem zero_ob_uniquely_isomorphic : forall (C : Cat) (A B : Ob),
    zero_object A -> zero_object B -> A ~~ B.
unfold zero_object; intros.
destruct H, H0; apply initial_ob_uniquely_isomorphic; assumption.
Qed.

Theorem mor_to_init_is_ret : forall (C : Cat) (I X : Ob) (f : Hom X I),
    initial I -> Ret f.
unfold initial, Ret; intros.
destruct (H X) as (g, [_ eq1]); destruct (H I) as (idI, [_ eq2]).
exists g.
rewrite <- (eq2 (g .> f)); [rewrite <- (eq2 (id I)); trivial | trivial].
Qed.

Theorem mor_to_term_is_sec : forall (C : Cat) (T X : Ob) (f : Hom T X),
    terminal T -> Sec f.
(*unfold terminal, Ret; intros.
destruct (H X) as (g, [_ eq1]); destruct (H T) as (idT, [_ eq2]).
exists g.
rewrite <- (eq2 (f .> g)); [rewrite <- (eq2 (id T)); trivial | trivial].
Restart.*)
intro C. rewrite <- (dual_involution C). intros.
rewrite dual_sec_ret. rewrite <- dual_initial_terminal in H.
apply mor_to_init_is_ret. assumption.
Qed.
