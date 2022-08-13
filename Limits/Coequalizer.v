From Cat Require Import Cat.
From Cat.Limits Require Import Equalizer.

Set Implicit Arguments.

Definition isCoequalizer
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (Q : Ob C) (q : Hom Y Q)
  (cofactorize : forall {Q' : Ob C} {q' : Hom Y Q'}, f .> q' == g .> q' -> Hom Q Q')
  : Prop :=
    f .> q == g .> q
      /\
    forall (Q' : Ob C) (q' : Hom Y Q') (H : f .> q' == g .> q'),
      setoid_unique (fun u : Hom Q Q' => q .> u == q') (cofactorize H).

Class HasCoequalizers (C : Cat) : Type :=
{
  coeq_ob :
    forall {X Y : Ob C} (f g : Hom X Y), Ob C;
  Proper_coeq_ob :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (id (coeq_ob f g)) (id (coeq_ob f' g'));
  coeq_mor :
    forall {X Y : Ob C} (f g : Hom X Y), Hom Y (coeq_ob f g);
  coeq_mor_ok :
    forall (X Y : Ob C) (f g : Hom X Y),
      f .> coeq_mor f g == g .> coeq_mor f g;
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
      isCoequalizer C f g (coeq_ob f g) (coeq_mor f g) (cofactorize f g)
}.

Arguments coeq_ob     [C _ X Y] _ _.
Arguments coeq_mor    [C _ X Y] _ _.
Arguments cofactorize [C _ X Y f g Q' q'] _.

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
  - destruct (Proper_eq_ob Y X f f' g g' H H0). auto.
  - apply eq_mor_ok.
  - destruct (Proper_eq_mor Y X f f' g g' H H0). auto.
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
  - destruct (Proper_coeq_ob Y X f f' g g' H H0). auto.
  - apply coeq_mor_ok.
  - destruct (Proper_coeq_mor Y X f f' g g' H H0). auto.
Defined.

Section HasCoequalizers.

Context
  [C : Cat]
  [X Y : Ob C]
  [f g : Hom X Y].

Lemma isEqualizer_Dual :
  forall
    (Q : Ob C) (q : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q'),
      @isEqualizer (Dual C) Y X f g Q q cofactorize
        =
      @isCoequalizer C X Y f g Q q cofactorize.
Proof. reflexivity. Defined.

Lemma isCoequalizer_Dual :
  forall
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      @isCoequalizer (Dual C) Y X f g E e factorize
        =
      @isEqualizer C X Y f g E e factorize.
Proof. reflexivity. Defined.

End HasCoequalizers.

Lemma isCoequalizer_uiso :
  forall
    [C : Cat] [X Y : Ob C] [f g : Hom X Y]
    (Q Q' : Ob C) (q : Hom Y Q) (q' : Hom Y Q')
    (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''), f .> q'' == g .> q'' -> Hom Q Q'')
    (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''), f .> q'' == g .> q'' -> Hom Q' Q''),
      isCoequalizer C f g Q q cofactorize -> isCoequalizer C f g Q' q' cofactorize' ->
        exists!! f : Hom Q' Q, isIso f /\ q' .> f == q.
Proof.
  intro. rewrite <- (Dual_Dual C). intros. cbn in *.
  rewrite isCoequalizer_Dual in *.
  destruct (isEqualizer_uiso H H0).
  exists x. repeat split.
    rewrite isIso_Dual. cat.
    cat. rewrite H3. reflexivity.
    intros. cat. apply H4. cat.
      rewrite isIso_Dual. assumption.
      rewrite H3. reflexivity.
Qed.

Lemma isEpi_coequalizer :
  forall
    [C : Cat] [X Y : Ob C] [f g : Hom X Y]
    (Q : Ob C) (q : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q'),
      isCoequalizer C f g Q q cofactorize -> isEpi q.
Proof.
  intro C. rewrite <- (Dual_Dual C); cbn; intros.
  rewrite isEpi_Dual.
  eapply isMono_equalizer.
  rewrite isCoequalizer_Dual in H.
  eassumption.
Qed.

Lemma isCoequalizer_mono_is_iso :
  forall
    [C : Cat] [X Y : Ob C] [f g : Hom X Y]
    (Q : Ob C) (q : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q'),
      isCoequalizer C f g Q q cofactorize -> isMono q -> isIso q.
Proof.
  intro C. rewrite <- (Dual_Dual C); cbn; intros.
  rewrite isIso_Dual.
  apply (@isEqualizer_epi_is_iso (Dual C) Y X f g _ _ cofactorize0).
  - rewrite isCoequalizer_Dual in H. exact H.
  - rewrite isEpi_Dual. exact H0.
Qed.

Section HasCoequalizers.

Context
  [C : Cat]
  [X Y : Ob C]
  [f g : Hom X Y].

Lemma isCoequalizer_iso :
  forall
    (Q Q' : Ob C) (q : Hom Y Q) (q' : Hom Y Q')
    (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''), f .> q'' == g .> q'' -> Hom Q Q'')
    (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''), f .> q'' == g .> q'' -> Hom Q' Q''),
      isCoequalizer C f g Q q cofactorize -> isCoequalizer C f g Q' q' cofactorize' -> Q ~ Q'.
Proof.
  intros. destruct (isCoequalizer_uiso H H0).
  do 2 destruct H1. iso.
Qed.

Lemma isCoequalizer_equiv :
  forall
    (Q : Ob C) (q1 : Hom Y Q) (q2 : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q'),
      isCoequalizer C f g Q q1 cofactorize -> isCoequalizer C f g Q q2 cofactorize -> q1 == q2.
Proof.
  intros. edestruct H, H0, (H4 _ _ H3).
  assert (cofactorize0 Q q2 H3 == id Q).
    apply H6. cat.
    edestruct (H2 _ _ H3). rewrite H7 in H8. cat.
Qed.

Lemma isCoequalizer_equiv_factorize :
  forall
    (Q : Ob C) (q : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q')
    (cofactorize' : forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' -> Hom Q Q'),
      isCoequalizer C f g Q q cofactorize -> isCoequalizer C f g Q q cofactorize' ->
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

End HasCoequalizers.