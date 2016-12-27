Require Export Cat.

Definition initial_object `{C : Cat} (I : Ob) : Prop :=
    forall (X : Ob), exists! f : Hom I X, True.

Definition terminal_object `{C : Cat} (T : Ob) : Prop :=
    forall (X : Ob), exists! f : Hom X T, True.

Definition zero_object `{_ : Cat} (Z : Ob) : Prop :=
    initial_object Z /\ terminal_object Z.

Definition has_initial_object `(C : Cat) : Prop :=
    exists I : Ob, initial_object I.

Definition has_terminal_object `(C : Cat) : Prop :=
    exists T : Ob, terminal_object T.

Definition has_zero_object `(C : Cat) : Prop :=
    exists Z : Ob, zero_object Z.

Theorem initial_ob_iso_unique : forall `(C : Cat) (I1 I2 : Ob),
    initial_object I1 -> initial_object I2 -> I1 ~ I2.
unfold initial_object, isomorphic; intros.
destruct (H I1) as (id1, [_ eq1]), (H0 I2) as (id2, [_ eq2]),
(H I2) as (f, _), (H0 I1) as (g, _); clear H H0.
exists f; unfold Iso; exists g; split.
rewrite <- (eq1 (f .> g)); [rewrite <- (eq1 (id I1)); trivial | trivial].
rewrite <- (eq2 (g .> f)); [rewrite <- (eq2 (id I2)); trivial | trivial].
Qed.

Theorem initial_ob_uniquely_isomorphic : forall `(C : Cat) (I1 I2 : Ob),
    initial_object I1 -> initial_object I2 -> I1 ~~ I2.
unfold uniquely_isomorphic; intros.
assert (I1 ~ I2). apply initial_ob_iso_unique; assumption.
destruct H1 as [f [g [eq1 eq2]]].
exists f. split. unfold Iso; exists g; split; assumption.
intros f' iso_f'. unfold initial_object in *.
destruct (H I2) as []. destruct H1.
assert (x = f). apply H2. trivial.
rewrite <- H3. apply H2. trivial.
Qed.

Theorem terminal_ob_iso_unique : forall `(C : Cat) (T1 T2 : Ob),
    terminal_object T1 -> terminal_object T2 -> T1 ~ T2.
unfold terminal_object, isomorphic; intros.
destruct (H T1) as (id1, [_ eq1]), (H0 T2) as (id2, [_ eq2]),
(H T2) as (f, _), (H0 T1) as (g, _); clear H H0.
exists g; unfold Iso; exists f; split.
rewrite <- (eq1 (g .> f)); [rewrite <- (eq1 (id T1)); trivial | trivial].
rewrite <- (eq2 (f .> g)); [rewrite <- (eq2 (id T2)); trivial | trivial].
Qed.

Theorem terminal_ob_uniquely_isomorphic : forall `(C : Cat) (T1 T2 : Ob),
    terminal_object T1 -> terminal_object T2 -> T1 ~~ T2.
unfold uniquely_isomorphic; intros.
assert (T1 ~ T2). apply terminal_ob_iso_unique; assumption.
destruct H1 as [f [g [eq1 eq2]]].
exists f. split. unfold Iso; exists g; split; assumption.
intros f' iso_f'. unfold terminal_object in *.
destruct (H0 T1) as []. destruct H1.
assert (x = f). apply H2. trivial.
rewrite <- H3. apply H2. trivial.
Qed.

Theorem zero_ob_uniquely_isomorphic : forall `(C : Cat) (Z1 Z2 : Ob),
    zero_object Z1 -> zero_object Z2 -> Z1 ~~ Z2.
unfold zero_object; intros.
destruct H, H0; apply initial_ob_uniquely_isomorphic; assumption.
Qed.

Theorem mor_to_init_is_ret : forall `(_ : Cat) (I X : Ob) (f : Hom X I),
    initial_object I -> Ret f.
unfold initial_object, Ret; intros.
destruct (H0 X) as (g, [_ eq1]); destruct (H0 I) as (idI, [_ eq2]).
exists g.
rewrite <- (eq2 (g .> f)); [rewrite <- (eq2 (id I)); trivial | trivial].
Qed.

Theorem mor_to_term_is_sec : forall `(_ : Cat) (T X : Ob) (f : Hom T X),
    terminal_object T -> Sec f.
unfold terminal_object, Ret; intros.
destruct (H0 X) as (g, [_ eq1]); destruct (H0 T) as (idT, [_ eq2]).
exists g.
rewrite <- (eq2 (f .> g)); [rewrite <- (eq2 (id T)); trivial | trivial].
Qed.
