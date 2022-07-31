From Cat Require Import Cat.
From Cat.Limits Require Import Equalizer.

Set Implicit Arguments.

Definition coequalizer
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (Q : Ob C) (q : Hom Y Q)
  (cofactorize : forall {Q' : Ob C} {q' : Hom Y Q'}, f .> q' == g .> q' -> Hom Q Q')
  : Prop :=
    f .> q == g .> q
      /\
    forall (Q' : Ob C) (q' : Hom Y Q') (H : f .> q' == g .> q'),
      setoid_unique (fun u : Hom Q Q' => q .> u == q') (cofactorize H).

Definition biequalizer
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (E : Ob C) (e : Hom E X) (q : Hom Y E)
  (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom E Q')
  : Prop :=
    equalizer C f g E e factorize /\
    coequalizer C f g E q cofactorize.

Class HasCoequalizers (C : Cat) : Type :=
{
  coeq_ob :
    forall {X Y : Ob C} (f g : Hom X Y), Ob C;
  Proper_coeq_ob :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (id (coeq_ob f g)) (id (coeq_ob f' g'));
  coeq_mor :
    forall {X Y : Ob C} (f g : Hom X Y), Hom Y (coeq_ob f g);
  Proper_coeq_mor :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (coeq_mor f g) (coeq_mor f' g');
  cofactorize :
    forall {X Y : Ob C} (f g : Hom X Y) (Q' : Ob C) (q' : Hom Y Q'),
      f .> q' == g .> q' -> Hom (coeq_ob f g) Q';
  (* TODO: Proper_cofactorize :
    forall
      (X Y Q' : Ob C) (f f' g g' : Hom X Y) (q' : Hom Y Q')
      (H : f .> q' == g .> q') (H' : f' .> q' == g' .> q'),
        f == f' -> g == g' -> JMequiv (cofactorize f g Q' q' H) (cofactorize f' g' Q' q' H'); *)
  is_coequalizer :
    forall (X Y : Ob C) (f g : Hom X Y),
      coequalizer C f g (coeq_ob f g) (coeq_mor f g) (cofactorize f g)
}.

Arguments coeq_ob     [C _ X Y] _ _.
Arguments coeq_mor    [C _ X Y] _ _.
Arguments cofactorize [C _ X Y f g Q' q'] _.

Class HasBiequalizers (C : Cat) : Type :=
{
  HasEqualizers_bi :> HasEqualizers C;
  HasCoequalizers_bi :> HasCoequalizers C;
  equalizer_is_coequalizer : forall (X Y : Ob C) (f g : Hom X Y), eq_ob f g = coeq_ob f g
}.

Coercion HasEqualizers_bi : HasBiequalizers >-> HasEqualizers.
Coercion HasCoequalizers_bi : HasBiequalizers >-> HasCoequalizers.

#[refine]
#[export]
Instance HasCoequalizers_Dual (C : Cat) (he : HasEqualizers C) : HasCoequalizers (Dual C) :=
{
  coeq_ob := fun X Y : Ob (Dual C) => @eq_ob C he Y X;
  coeq_mor := fun X Y : Ob (Dual C) => @eq_mor C he Y X;
  cofactorize := fun X Y : Ob (Dual C) => @factorize C he Y X;
  is_coequalizer := fun X Y : Ob (Dual C) => @is_equalizer C he Y X
}.
Proof.
  all: cbn; intros.
    destruct (Proper_eq_ob Y X f f' g g' H H0). auto.
    destruct (Proper_eq_mor Y X f f' g g' H H0). auto.
Defined.

#[refine]
#[export]
Instance HasEqualizers_Dual (C : Cat) (he : HasCoequalizers C) : HasEqualizers (Dual C) :=
{
  eq_ob := fun X Y : Ob (Dual C) => @coeq_ob C he Y X;
  eq_mor := fun X Y : Ob (Dual C) => @coeq_mor C he Y X;
  factorize := fun X Y : Ob (Dual C) => @cofactorize C he Y X;
  is_equalizer := fun X Y : Ob (Dual C) => @is_coequalizer C he Y X
}.
Proof.
  all: cbn; intros.
    destruct (Proper_coeq_ob Y X f f' g g' H H0). auto.
    destruct (Proper_coeq_mor Y X f f' g g' H H0). auto.
Defined.

#[refine]
#[export]
Instance HasBiequalizers_Dual (C : Cat) (he : HasBiequalizers C) : HasBiequalizers (Dual C) :=
{
  HasEqualizers_bi := HasEqualizers_Dual he;
  HasCoequalizers_bi := HasCoequalizers_Dual he;
}.
Proof.
  simpl. intros. rewrite equalizer_is_coequalizer. trivial.
Defined.

Section HasCoequalizers.

Context
  [C : Cat]
  [X Y : Ob C]
  [f g : Hom X Y].

Lemma dual_equalizer_coequalizer :
  forall
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      @equalizer C X Y f g E e factorize
        <->
      @coequalizer (Dual C) Y X f g E e factorize.
Proof. cat. Qed.

Lemma dual_biqualizer_self :
  forall
    (E : Ob C) (e : Hom E X) (q : Hom Y E)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E)
    (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom E Q'),
      @biequalizer C X Y f g E e q factorize cofactorize
        <->
      @biequalizer (Dual C) Y X f g E q e cofactorize factorize.
Proof.
  unfold biequalizer. do 2 split; destruct H; assumption.
Qed.

End HasCoequalizers.

Lemma coequalizer_uiso :
  forall
    [C : Cat] [X Y : Ob C] [f g : Hom X Y]
    (Q Q' : Ob C) (q : Hom Y Q) (q' : Hom Y Q')
    (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''), f .> q'' == g .> q'' -> Hom Q Q'')
    (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''), f .> q'' == g .> q'' -> Hom Q' Q''),
      coequalizer C f g Q q cofactorize -> coequalizer C f g Q' q' cofactorize' ->
        exists!! f : Hom Q' Q, isIso f /\ q' .> f == q.
Proof.
  intro. rewrite <- (Dual_Dual C). intros. cbn in *.
  rewrite <- dual_equalizer_coequalizer in H.
  rewrite <- dual_equalizer_coequalizer in H0.
  destruct (equalizer_uiso H H0).
  exists x. repeat split.
    rewrite <- Dual_isIso. cat.
    cat. rewrite H3. reflexivity.
    intros. cat. apply H4. cat.
      rewrite Dual_isIso. assumption.
      rewrite H3. reflexivity.
Qed.

Lemma isEpi_coequalizer :
  forall
    [C : Cat] [X Y : Ob C] [f g : Hom X Y]
    (Q : Ob C) (q : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q'),
      coequalizer C f g Q q cofactorize -> isEpi q.
Proof.
  intro C. rewrite <- (Dual_Dual C); cbn; intros.
  rewrite <- Dual_isMono_isEpi.
  rewrite <- dual_equalizer_coequalizer in *.
  eapply isMono_equalizer. eauto.
Qed.

Lemma coequalizer_mono_is_iso :
  forall
    [C : Cat] [X Y : Ob C] [f g : Hom X Y]
    (Q : Ob C) (q : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q'),
      coequalizer C f g Q q cofactorize -> isMono q -> isIso q.
Proof.
  intro C. rewrite <- (Dual_Dual C); cbn; intros.
  rewrite Dual_isMono_isEpi in H0.
  rewrite <- Dual_isIso.
  apply (@equalizer_epi_is_iso (Dual C) Y X f g _ _ cofactorize0).
    rewrite dual_equalizer_coequalizer. exact H.
    exact H0.
Qed.

Section HasCoequalizers.

Context
  [C : Cat]
  [X Y : Ob C]
  [f g : Hom X Y].

Lemma coequalizer_iso :
  forall
    (Q Q' : Ob C) (q : Hom Y Q) (q' : Hom Y Q')
    (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''), f .> q'' == g .> q'' -> Hom Q Q'')
    (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''), f .> q'' == g .> q'' -> Hom Q' Q''),
      coequalizer C f g Q q cofactorize -> coequalizer C f g Q' q' cofactorize' -> Q ~ Q'.
Proof.
  intros. destruct (coequalizer_uiso H H0).
  do 2 destruct H1. iso.
Qed.

Lemma coequalizer_equiv :
  forall
    (Q : Ob C) (q1 : Hom Y Q) (q2 : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q'),
      coequalizer C f g Q q1 cofactorize -> coequalizer C f g Q q2 cofactorize -> q1 == q2.
Proof.
  intros. edestruct H, H0, (H4 _ _ H3).
  assert (cofactorize0 Q q2 H3 == id Q).
    apply H6. cat.
    edestruct (H2 _ _ H3). rewrite H7 in H8. cat.
Qed.

Lemma coequalizer_equiv_factorize :
  forall
    (Q : Ob C) (q : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q')
    (cofactorize' : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q'),
      coequalizer C f g Q q cofactorize -> coequalizer C f g Q q cofactorize' ->
        forall (Q' : Ob C) (q' : Hom Y Q') (H : f .> q' == g .> q'),
          cofactorize Q' q' H == cofactorize' Q' q' H.
Proof.
  intros.
  edestruct H, H3; apply H5.
  edestruct H0, H7; apply H8.
Qed.

Lemma cofactorize_eq_mor :
  forall (C : Cat) (he : HasCoequalizers C) (X Y : Ob C) (f g : Hom X Y),
    cofactorize (proj1 (is_coequalizer X Y f g)) == id (coeq_ob f g).
Proof.
  intros. destruct he; cbn in *.
  edestruct is_coequalizer0, s. cat.
Defined.

(* TODO : finish *) Lemma biequalizer_uiso :
  forall
    (E : Ob C) (e : Hom E X) (q : Hom Y E)
    (factorize : forall (E'' : Ob C) (e'' : Hom E'' X), e'' .> f == e'' .> g -> Hom E'' E)
    (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''), f .> q'' == g .> q'' -> Hom E Q'')
    (E' : Ob C) (e' : Hom E' X) (q' : Hom Y E')
    (factorize' : forall (E'' : Ob C) (e'' : Hom E'' X), e'' .> f == e'' .> g -> Hom E'' E')
    (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''), f .> q'' == g .> q'' -> Hom E' Q''),
      biequalizer C f g E e q factorize cofactorize ->
      biequalizer C f g E' e' q' factorize' cofactorize' ->
        exists!! f : Hom E E', isIso f /\ e == f .> e' /\ q .> f == q'.
Proof.
  unfold biequalizer; intros.
  destruct H as [[HE_eq HE_uq] [HC_eq HC_uq]],
    H0 as [[HE'_eq HE'_uq] [HC'_eq HC'_uq]].
  destruct (HE_uq E' e' HE'_eq) as [eq unique].
  destruct (HE'_uq E e HE_eq) as [eq' unique'].
  exists (factorize' E e HE_eq).
  repeat split.
    red. exists (factorize E' e' HE'_eq). split. (*
      destruct (HE_uq E (factorize' E e HE_eq .> e')). rewrite eq'. auto.
        rewrite <- (H0 (factorize' E e .> factorize0 E' e')).
        apply H0. rewrite eq'. cat.
        rewrite comp_assoc, eq. reflexivity.
      destruct (HE'_uq E' (factorize0 E' e' .> e)). rewrite eq. auto.
        rewrite <- (H0 (factorize0 E' e' .> factorize' E e)).
        apply H0. rewrite eq. cat.
        rewrite comp_assoc, eq'. reflexivity.
    rewrite eq'. reflexivity.
    Focus 2.
    intros. destruct H as [_ [H1 _]]. apply unique'. symmetry. auto.
    destruct (HC_uq E' q' HC'_eq).
    destruct (HC'_uq E q HC_eq).
    assert (factorize' E e .> e' .> g .> q'
      == e .> f .> q .> cofactorize0 E' q').
      rewrite eq'. rewrite HE_eq.
      assocr'. rewrite H. reflexivity. rewrite unique'. eauto.
        rewrite H0. eauto.
    assert (factorize' E e == cofactorize0 E' q').
      apply unique'. *)
Abort.

End HasCoequalizers.