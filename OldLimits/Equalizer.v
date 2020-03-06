Require Import Cat.

Definition equalizer (C : Cat) {X Y : Ob C} (f g : Hom X Y)
    (E : Ob C) (e : Hom E X) : Prop := e .> f == e .> g /\
    forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g ->
    exists!! u : Hom E' E, u .> e == e'.

Definition coequalizer (C : Cat) {X Y : Ob C} (f g : Hom X Y)
    (Q : Ob C) (q : Hom Y Q) : Prop := f .> q == g .> q /\
    forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' ->
    exists!! u : Hom Q Q', q .> u == q'.

Definition biequalizer (C : Cat) {X Y : Ob C} (f g : Hom X Y)
    (E : Ob C) (e : Hom E X) (q : Hom Y E) : Prop :=
    equalizer C f g E e /\ coequalizer C f g E q.

Class has_equalizers (C : Cat) : Type :=
{
    eq_ob : forall {X Y : Ob C} (f g : Hom X Y), Ob C;
    eq_mor : forall {X Y : Ob C} (f g : Hom X Y), Hom (eq_ob f g) X;
    is_equalizer :
      forall (X Y : Ob C) (f g : Hom X Y),
        equalizer C f g (eq_ob f g) (eq_mor f g)
}.

Class has_coequalizers (C : Cat) : Type :=
{
    coeq_ob : forall {X Y : Ob C} (f g : Hom X Y), Ob C;
    coeq_mor : forall {X Y : Ob C} (f g : Hom X Y), Hom Y (coeq_ob f g);
    is_coequalizer : forall (X Y : Ob C) (f g : Hom X Y),
        coequalizer C f g (coeq_ob f g) (coeq_mor f g)
}.

Class has_biequalizers (C : Cat) : Type :=
{
    bi_has_equalizers :> has_equalizers C;
    bi_has_coequalizers :> has_coequalizers C;
    equalizer_is_coequalizer : forall (X Y : Ob C) (f g : Hom X Y),
        eq_ob f g = coeq_ob f g
}.

Coercion bi_has_equalizers : has_biequalizers >-> has_equalizers.
Coercion bi_has_coequalizers : has_biequalizers >-> has_coequalizers.

Theorem dual_equalizer_coequalizer : forall (C : Cat) (X Y E : Ob C)
    (f g : Hom X Y) (e : Hom E X),
    @equalizer C X Y f g E e <-> @coequalizer (Dual C) Y X f g E e.
Proof. unfold equalizer, coequalizer. cat. Qed.

Theorem dual_biqualizer_self : forall (C : Cat) (X Y E : Ob C)
    (f g : Hom X Y) (e : Hom E X) (q : Hom Y E),
    @biequalizer C X Y f g E e q <-> @biequalizer (Dual C) Y X f g E q e.
Proof. unfold biequalizer, equalizer, coequalizer. cat. Qed.

Theorem equalizer_iso : forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E E' : Ob C) (e : Hom E X) (e' : Hom E' X),
    equalizer C f g E e -> equalizer C f g E' e' -> E ~ E'.
Proof.
  unfold equalizer; intros. destruct H, H0.
  destruct (H1 E' e' H0) as [h [eq unique]].
  destruct (H2 E e H) as [h' [eq' unique']].
  red. exists h'. red. exists h. split.
    destruct (H1 E (h' .> e')). rewrite eq'. auto.
      red in H3. destruct H3.
      rewrite <- (H4 (h' .> h)).
      apply H4. rewrite eq'. cat.
      rewrite comp_assoc, eq. reflexivity.
    destruct (H2 E' (h .> e)). rewrite eq. auto.
      red in H3. destruct H3.
      rewrite <- (H4 (h .> h')).
      apply H4. rewrite eq. cat.
      rewrite comp_assoc, eq'. reflexivity.
Qed.

Theorem coequalizer_iso : forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (Q Q' : Ob C) (q : Hom Y Q) (q' : Hom Y Q'),
    coequalizer C f g Q q -> coequalizer C f g Q' q' -> Q ~ Q'.
Proof.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite <- dual_equalizer_coequalizer in *.
  rewrite dual_isomorphic_self. eapply equalizer_iso.
  exact H0. exact H.
Defined.

Theorem biequalizer_iso : forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E E' : Ob C) (e : Hom E X) (q : Hom Y E) (e' : Hom E' X) (q' : Hom Y E'),
    biequalizer C f g E e q -> biequalizer C f g E' e' q' -> E ~ E'.
Proof.
  unfold biequalizer; intros. destruct H, H0.
  eapply equalizer_iso; eauto.
Qed.

Theorem equalizer_is_mono : forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E : Ob C) (e : Hom E X), equalizer C f g E e -> Mon e.
Proof.
  unfold equalizer, Mon. intros.
  rename X0 into Z. rename g0 into h'.
  destruct H as [eq H].
  destruct (H Z (h .> e)) as [u Hh].
    rewrite !comp_assoc, eq. reflexivity.
  destruct (H Z (h' .> e)) as [u' Hh'].
    rewrite !comp_assoc, eq. reflexivity.
  destruct Hh, Hh'. assert (u' == u).
    apply H4. rewrite H1, H0. reflexivity.
  specialize (H2 h); specialize (H4 h').
  rewrite <- H2, <- H4; try assumption; reflexivity.
Defined.

Theorem coequalizer_is_epi : forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (Q : Ob C) (q : Hom Y Q), coequalizer C f g Q q -> Epi q.
Proof.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite <- dual_mon_epi.
  rewrite <- dual_equalizer_coequalizer in *.
  eapply equalizer_is_mono. eauto.
Defined.

Instance Dual_has_coequalizers (C : Cat) (he : has_equalizers C)
    : has_coequalizers (Dual C) :=
{
    coeq_ob := fun X Y : Ob (Dual C) => @eq_ob C he Y X;
    coeq_mor := fun X Y : Ob (Dual C) => @eq_mor C he Y X;
    is_coequalizer := fun X Y : Ob (Dual C) => @is_equalizer C he Y X
}.

Instance Dual_has_equalizers (C : Cat) (he : has_coequalizers C)
    : has_equalizers (Dual C) :=
{
    eq_ob := fun X Y : Ob (Dual C) => @coeq_ob C he Y X;
    eq_mor := fun X Y : Ob (Dual C) => @coeq_mor C he Y X;
    is_equalizer := fun X Y : Ob (Dual C) => @is_coequalizer C he Y X
}.

#[refine]
Instance Dual_has_biequalizers (C : Cat) (he : has_biequalizers C)
    : has_biequalizers (Dual C) :=
{
    bi_has_equalizers := Dual_has_equalizers C he;
    bi_has_coequalizers := Dual_has_coequalizers C he;
}.
Proof.
  simpl. intros. rewrite equalizer_is_coequalizer. trivial.
Defined.