Require Export Cat.

Set Universe Polymorphism.

Definition equalizer (C : Cat) {X Y : Ob C} (f g : Hom X Y)
    (E : Ob C) (e : Hom E X) : Prop := e .> f == e .> g /\
    forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g ->
    exists!! u : Hom E' E, u .> e == e'.

Definition coequalizer (C : Cat) {X Y : Ob C} (f g : Hom X Y)
    (Q : Ob C) (q : Hom Y Q) : Prop := f .> q == g .> q /\
    forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' ->
    exists!! u : Hom Q Q', q .> u == q'.

Theorem dual_equalizer_coequalizer : forall (C : Cat) (X Y E : Ob C)
    (f g : Hom X Y) (e : Hom E X),
    @equalizer C X Y f g E e <-> @coequalizer (Dual C) Y X f g E e.
Proof. unfold equalizer, coequalizer. cat. Qed.

Class has_equalizers (C : Cat) : Type :=
{
    eq_ob : forall (X Y : Ob C) (f g : Hom X Y), Ob C;
    eq_mor : forall (X Y : Ob C) (f g : Hom X Y), Hom (eq_ob X Y f g) X;
    is_equalizer : forall (X Y : Ob C) (f g : Hom X Y),
        equalizer C f g (eq_ob X Y f g) (eq_mor X Y f g)
}.

Class has_coequalizers (C : Cat) : Type :=
{
    coeq_ob : forall (X Y : Ob C) (f g : Hom X Y), Ob C;
    coeq_mor : forall (X Y : Ob C) (f g : Hom X Y), Hom Y (coeq_ob X Y f g);
    is_coequalizer : forall (X Y : Ob C) (f g : Hom X Y),
        coequalizer C f g (coeq_ob X Y f g) (coeq_mor X Y f g)
}.

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

