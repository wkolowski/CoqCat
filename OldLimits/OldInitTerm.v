Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.

Definition initial {C : Cat} (I : Ob C) : Prop :=
    forall (X : Ob C), exists!! f : Hom I X, True.

Definition terminal {C : Cat} (T : Ob C) : Prop :=
    forall (X : Ob C), exists!! f : Hom X T, True.

Definition zero_object {C : Cat} (Z : Ob C) : Prop :=
    initial Z /\ terminal Z.

Hint Unfold initial terminal zero_object.

Theorem dual_initial_terminal : forall (C : Cat) (A : Ob C),
    @initial C A <-> @terminal (Dual C) A.
Proof. split; auto. Qed.

Theorem dual_zero_self : forall (C : Cat) (A : Ob C),
    @zero_object C A <-> @zero_object (Dual C) A.
Proof.
  unfold zero_object; repeat split; intros;
  destruct H; assumption.
Qed.

Theorem initial_uiso : forall (C : Cat) (A B : Ob C),
    initial A -> initial B -> A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic, initial; intros.
  destruct (H B) as [f [_ Hf]],
           (H0 A) as [g [_ Hg]],
           (H A) as [idA [_ HA]],
           (H0 B) as [idB [_ HB]].
  exists f; red. split; auto. exists g; split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Qed.

Hint Resolve initial_uiso.

Theorem initial_iso : forall (C : Cat) (A B : Ob C),
    initial A -> initial B -> A ~ B.
Proof. auto. Defined.

Theorem terminal_uiso : forall (C : Cat) (A B : Ob C),
    terminal A -> terminal B -> A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic, terminal; intros.
  destruct (H B) as [f [_ Hf]], (H0 A) as [g [_ Hg]], (H A) as [idA [_ HA]],
    (H0 B) as [idB [_ HB]].
  exists g; red. split; auto. exists f; split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Restart.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite <- dual_initial_terminal in *.
  rewrite dual_unique_iso_self. cat.
Qed.

Hint Resolve terminal_uiso.

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

Theorem iso_to_init_is_init : forall (C : Cat) (I X : Ob C),
    initial I -> I ~ X -> initial X.
Proof.
  intros. destruct H0 as [f [g [eq1 eq2]]].
  unfold initial in *. intro X'.
  destruct (H X') as [create [_ Hcreate]].
  exists (g .> create). split; intros; auto.
    specialize (Hcreate (f .> y) H0). rewrite Hcreate.
      rewrite <- comp_assoc. rewrite eq2. rewrite id_left. reflexivity.
Defined.

Theorem iso_to_term_is_term : forall (C : Cat) (T X : Ob C),
    terminal T -> T ~ X -> terminal X.
Proof.
  intros. destruct H0 as [f [g [eq1 eq2]]].
  unfold terminal in *. intro X'.
  destruct (H X') as [del [_ Hdel]].
  exists (del .> f). split; intros; auto.
    specialize (Hdel (y .> g) H0). rewrite Hdel.
      rewrite comp_assoc. rewrite eq2. rewrite id_right. reflexivity.
Qed.

Theorem mor_to_init_is_ret : forall (C : Cat) (I X : Ob C) (f : Hom X I),
    initial I -> Ret f.
Proof.
  unfold initial, Ret; intros.
  destruct (H X) as (g, [_ eq1]), (H I) as (idI, [_ eq2]). exists g.
  rewrite <- (eq2 (g .> f)); try rewrite <- (eq2 (id I)); reflexivity.
Qed.

Theorem mor_from_term_is_sec : forall (C : Cat) (T X : Ob C) (f : Hom T X),
    terminal T -> Sec f.
Proof.
  unfold terminal, Sec; intros.
  destruct (H X) as (g, [_ eq1]), (H T) as (idT, [_ eq2]). exists g.
  rewrite <- (eq2 (f .> g)); try rewrite <- (eq2 (id T)); reflexivity.
Qed.