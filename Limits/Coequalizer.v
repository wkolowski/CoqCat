From Cat Require Import Cat.
From Cat.Limits Require Import Equalizer.

Set Implicit Arguments.

Definition isCoequalizer
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (Q : Ob C) (q : Hom Y Q)
  (cofactorize : forall {Q' : Ob C} {q2 : Hom Y Q'}, f .> q2 == g .> q2 -> Hom Q Q')
  : Prop :=
    f .> q == g .> q
      /\
    forall (Q' : Ob C) (q2 : Hom Y Q') (H : f .> q2 == g .> q2),
      setoid_unique (fun u : Hom Q Q' => q .> u == q2) (cofactorize H).

Class HasCoequalizers (C : Cat) : Type :=
{
  coequalizer :
    forall {X Y : Ob C} (f g : Hom X Y), Ob C;
  Proper_coequalizer :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (id (coequalizer f g)) (id (coequalizer f' g'));
  coeq_mor :
    forall {X Y : Ob C} (f g : Hom X Y), Hom Y (coequalizer f g);
  coeq_mor_ok :
    forall (X Y : Ob C) (f g : Hom X Y),
      f .> coeq_mor f g == g .> coeq_mor f g;
  Proper_coeq_mor :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (coeq_mor f g) (coeq_mor f' g');
  cofactorize :
    forall {X Y : Ob C} (f g : Hom X Y) (Q' : Ob C) (q2 : Hom Y Q'),
      f .> q2 == g .> q2 -> Hom (coequalizer f g) Q';
  (* TODO: Proper_cofactorize :
    forall
      (X Y Q' : Ob C) (f f' g g' : Hom X Y) (q2 : Hom Y Q')
      (H : f .> q2 == g .> q2) (H' : f' .> q2 == g' .> q2),
        f == f' -> g == g' -> JMequiv (cofactorize f g Q' q2 H) (cofactorize f' g' Q' q2 H'); *)
  is_coequalizer :
    forall (X Y : Ob C) (f g : Hom X Y),
      isCoequalizer C f g (coequalizer f g) (coeq_mor f g) (cofactorize f g)
}.

Arguments coequalizer     [C _ X Y] _ _.
Arguments coeq_mor    [C _ X Y] _ _.
Arguments cofactorize [C _ X Y f g Q' q2] _.

#[refine]
#[export]
Instance HasCoequalizers_Dual (C : Cat) (he : HasEqualizers C) : HasCoequalizers (Dual C) :=
{
  coequalizer := fun X Y : Ob (Dual C) => @equalizer C he Y X;
  coeq_mor := fun X Y : Ob (Dual C) => @eq_mor C he Y X;
  cofactorize := fun X Y : Ob (Dual C) => @factorize C he Y X;
  is_coequalizer := fun X Y : Ob (Dual C) => @is_equalizer C he Y X
}.
Proof.
  all: cbn; intros.
  - destruct (Proper_equalizer Y X f f' g g' H H0). auto.
  - apply eq_mor_ok.
  - destruct (Proper_eq_mor Y X f f' g g' H H0). auto.
Defined.

#[refine]
#[export]
Instance HasEqualizers_Dual (C : Cat) (he : HasCoequalizers C) : HasEqualizers (Dual C) :=
{
  equalizer := fun X Y : Ob (Dual C) => @coequalizer C he Y X;
  eq_mor := fun X Y : Ob (Dual C) => @coeq_mor C he Y X;
  factorize := fun X Y : Ob (Dual C) => @cofactorize C he Y X;
  is_equalizer := fun X Y : Ob (Dual C) => @is_coequalizer C he Y X
}.
Proof.
  all: cbn; intros.
  - destruct (Proper_coequalizer Y X f f' g g' H H0). auto.
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
    (cofactorize : forall (Q' : Ob C) (q2 : Hom Y Q'), f .> q2 == g .> q2 -> Hom Q Q'),
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
    (Q1 : Ob C) (q1 : Hom Y Q1)
    (cofactorize1 : forall (Q1' : Ob C) (q1' : Hom Y Q1'), f .> q1' == g .> q1' -> Hom Q1 Q1')
    (Q2 : Ob C) (q2 : Hom Y Q2)
    (cofactorize2 : forall (Q2' : Ob C) (q2' : Hom Y Q2'), f .> q2' == g .> q2' -> Hom Q2 Q2'),
      isCoequalizer C f g Q1 q1 cofactorize1 ->
      isCoequalizer C f g Q2 q2 cofactorize2 ->
        exists!! f : Hom Q2 Q1, isIso f /\ q2 .> f == q1.
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

Lemma isCoequalizer_iso :
  forall
    [C : Cat] [X Y : Ob C] [f g : Hom X Y]
    (Q1 : Ob C) (q1 : Hom Y Q1)
    (cofactorize1 : forall (Q1' : Ob C) (q1' : Hom Y Q1'), f .> q1' == g .> q1' -> Hom Q1 Q1')
    (Q2 : Ob C) (q2 : Hom Y Q2)
    (cofactorize2 : forall (Q2' : Ob C) (q2' : Hom Y Q2'), f .> q2' == g .> q2' -> Hom Q2 Q2'),
      isCoequalizer C f g Q1 q1 cofactorize1 ->
      isCoequalizer C f g Q2 q2 cofactorize2 ->
        Q1 ~ Q2.
Proof.
  intros. destruct (isCoequalizer_uiso H H0).
  do 2 destruct H1. iso.
Qed.

Lemma isEpi_coequalizer :
  forall
    [C : Cat] [X Y : Ob C] [f g : Hom X Y]
    (Q : Ob C) (q : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q2 : Hom Y Q'), f .> q2 == g .> q2 -> Hom Q Q'),
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
    (cofactorize : forall (Q' : Ob C) (q2 : Hom Y Q'), f .> q2 == g .> q2 -> Hom Q Q'),
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

Lemma isCoequalizer_equiv :
  forall
    (Q : Ob C) (q1 q2 : Hom Y Q)
    (cofactorize : forall (Q' : Ob C) (q2 : Hom Y Q'), f .> q2 == g .> q2 -> Hom Q Q'),
      isCoequalizer C f g Q q1 cofactorize ->
      isCoequalizer C f g Q q2 cofactorize ->
        q1 == q2.
Proof.
  intros. edestruct H, H0, (H4 _ _ H3).
  assert (cofactorize0 Q q2 H3 == id Q).
    apply H6. cat.
    edestruct (H2 _ _ H3). rewrite H7 in H8. cat.
Qed.

Lemma isCoequalizer_equiv_factorize :
  forall
    (Q : Ob C) (q : Hom Y Q)
    (cofactorize1 cofactorize2 : forall (Q' : Ob C) (q2 : Hom Y Q'), f .> q2 == g .> q2 -> Hom Q Q'),
      isCoequalizer C f g Q q cofactorize1 ->
      isCoequalizer C f g Q q cofactorize2 ->
        forall (Q' : Ob C) (q' : Hom Y Q') (H : f .> q' == g .> q'),
          cofactorize1 Q' q' H == cofactorize2 Q' q' H.
Proof.
  intros.
  edestruct H, H3; apply H5.
  edestruct H0, H7; apply H8.
Qed.

Lemma cofactorize_eq_mor :
  forall (C : Cat) (he : HasCoequalizers C) (X Y : Ob C) (f g : Hom X Y),
    cofactorize (proj1 (is_coequalizer X Y f g)) == id (coequalizer f g).
Proof.
  intros. destruct he; cbn in *.
  edestruct is_coequalizer0, s. cat.
Defined.

End HasCoequalizers.