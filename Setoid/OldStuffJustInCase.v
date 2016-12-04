(*Theorem initial_ob_iso_unique : forall (C : Cat) (A B : Ob C),
    initial A -> initial B -> A ~ B.
unfold initial, isomorphic; intros.
destruct (H A) as (id1, [_ eq1]), (H0 B) as (id2, [_ eq2]),
(H B) as (f, _), (H0 A) as (g, _); clear H H0.
exists f; unfold Iso; exists g; split.
rewrite <- (eq1 (f .> g)); [rewrite <- (eq1 (id A)); trivial | trivial].
  reflexivity.
rewrite <- (eq2 (g .> f)); [rewrite <- (eq2 (id B)); trivial | trivial].
  reflexivity.
Qed.

Theorem initial_ob_uniquely_isomorphic : forall (C : Cat) (A B : Ob C),
    initial A -> initial B -> A ~~ B.
unfold uniquely_isomorphic; intros.
assert (A ~ B). apply initial_ob_iso_unique; assumption.
destruct H1 as [f [g [eq1 eq2]]].
exists f. split. unfold Iso; exists g; split; assumption.
intros f' iso_f'. unfold initial in *.
destruct (H B) as []. destruct H1.
assert (x == f). apply H2. trivial.
rewrite <- H3. apply H2. trivial.
Qed.*)


(*Theorem terminal_ob_iso_unique : forall (C : Cat) (A B : Ob C),
    terminal A -> terminal B -> A ~ B.
unfold terminal, isomorphic; intros.
destruct (H A) as (id1, [_ eq1]), (H0 B) as (id2, [_ eq2]),
(H B) as (f, _), (H0 A) as (g, _); clear H H0.
exists g; unfold Iso; exists f; split.
rewrite <- (eq1 (g .> f)); try rewrite <- (eq1 (id A)); reflexivity.
rewrite <- (eq2 (f .> g)); try rewrite <- (eq2 (id B)); reflexivity.
Qed.

Theorem terminal_ob_uniquely_isomorphic : forall (C : Cat) (A B : Ob C),
    terminal A -> terminal B -> A ~~ B.
unfold uniquely_isomorphic; intros.
assert (A ~ B). apply terminal_ob_iso_unique; assumption.
destruct H1 as [f [g [eq1 eq2]]].
exists f. split. unfold Iso; exists g; split; assumption.
intros f' iso_f'. unfold terminal in *.
destruct (H0 A) as []. destruct H1.
assert (x == f). apply H2. trivial.
rewrite <- H3. apply H2. trivial.
Qed.*)

(*Theorem zero_ob_uniquely_isomorphic : forall (C : Cat) (A B : Ob C),
    zero_object A -> zero_object B -> A ~~ B.
Proof.
  unfold zero_object; intros.
  destruct H, H0; apply initial_ob_uniquely_isomorphic; assumption.
Qed.*)