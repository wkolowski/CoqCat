Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Cat.

Definition equalizer_skolem
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (E : Ob C) (e : Hom E X)
  (factorize : forall {E' : Ob C} (e' : Hom E' X), Hom E' E) : Prop :=
    e .> f == e .> g /\
    forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g ->
      setoid_unique (fun u : Hom E' E => u .> e == e') (factorize e').

Definition coequalizer_skolem
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (Q : Ob C) (q : Hom Y Q)
  (cofactorize : forall {Q' : Ob C} (q' : Hom Y Q'), Hom Q Q') : Prop :=
    f .> q == g .> q /\
    forall (Q' : Ob C) (q' : Hom Y Q'), f .> q' == g .> q' ->
      setoid_unique (fun u : Hom Q Q' => q .> u == q') (cofactorize q').

Definition biequalizer_skolem
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (E : Ob C) (e : Hom E X) (q : Hom Y E)
  (factorize : forall (E' : Ob C) (e' : Hom E' X), Hom E' E)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), Hom E Q') : Prop :=
    equalizer_skolem C f g E e factorize /\
    coequalizer_skolem C f g E q cofactorize.

Inductive JMequiv {A : Type} {is_setoid : Setoid A} (x : A)
    : forall {B : Type}, B -> Prop :=
    | JMequiv_refl : forall y : A, x == y -> JMequiv x y.

(* TODO : check coherences for has_equalizers *)
Class has_equalizers (C : Cat) : Type :=
{
    eq_ob : forall {X Y : Ob C}, Hom X Y -> Hom X Y -> Ob C;
    eq_mor : forall {X Y : Ob C} (f g : Hom X Y), Hom (eq_ob f g) X;
    eq_mor_Proper : forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (eq_mor f g) (eq_mor f' g');
    factorize : forall {X Y : Ob C} (f g : Hom X Y)
      (E' : Ob C) (e' : Hom E' X), Hom E' (eq_ob f g);
    factorize_Proper : forall (X Y E' : Ob C) (f g : Hom X Y),
      Proper (equiv ==> equiv) (@factorize X Y f g E');
    is_equalizer : forall (X Y : Ob C) (f g : Hom X Y),
        equalizer_skolem C f g
          (eq_ob f g) (eq_mor f g) (factorize f g)
}.

(* TODO : check coherences for has_coequalizers *)
Class has_coequalizers (C : Cat) : Type :=
{
    coeq_ob : forall {X Y : Ob C} (f g : Hom X Y), Ob C;
    coeq_mor : forall {X Y : Ob C} (f g : Hom X Y), Hom Y (coeq_ob f g);
    coeq_mor_Proper : forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (coeq_mor f g) (coeq_mor f' g');
    cofactorize : forall {X Y : Ob C} (f g : Hom X Y)
      (Q' : Ob C) (q' : Hom Y Q'), Hom (coeq_ob f g) Q';
    is_coequalizer : forall (X Y : Ob C) (f g : Hom X Y),
        coequalizer_skolem C f g
          (coeq_ob f g) (coeq_mor f g) (cofactorize f g)
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

Theorem dual_equalizer_coequalizer_skolem :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), Hom E' E),
      @equalizer_skolem C X Y f g E e factorize <->
      @coequalizer_skolem (Dual C) Y X f g E e factorize.
Proof. cat. Qed.

Theorem dual_biqualizer_skolem_self :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (E : Ob C) (e : Hom E X) (q : Hom Y E)
  (factorize : forall (E' : Ob C) (e' : Hom E' X), Hom E' E)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), Hom E Q'),
    @biequalizer_skolem C X Y f g E e q factorize cofactorize <->
    @biequalizer_skolem (Dual C) Y X f g E q e cofactorize factorize.
Proof.
  unfold biequalizer_skolem. do 2 split.
    destruct H. apply dual_equalizer_coequalizer_skolem. assumption.
    destruct H. apply dual_equalizer_coequalizer_skolem. assumption.
    destruct H. apply dual_equalizer_coequalizer_skolem. assumption.
    destruct H. rewrite dual_equalizer_coequalizer_skolem in H. exact H.
Qed.

Theorem equalizer_skolem_uiso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E E' : Ob C) (e : Hom E X) (e' : Hom E' X)
    (factorize : forall (E'' : Ob C) (e'' : Hom E'' X), Hom E'' E)
    (factorize' : forall (E'' : Ob C) (e'' : Hom E'' X), Hom E'' E'),
      equalizer_skolem C f g E e factorize ->
      equalizer_skolem C f g E' e' factorize' ->
      exists !! f : Hom E E', Iso f /\
        e == f .> e'.
Proof.
  unfold equalizer_skolem; intros. destruct H, H0.
  destruct (H1 E' e' H0) as [eq unique].
  destruct (H2 E e H) as [eq' unique'].
  exists (factorize' E e).
  repeat split.
    red. exists (factorize0 E' e'). split.
      destruct (H1 E (factorize' E e .> e')). rewrite eq'. auto.
        rewrite <- (H4 (factorize' E e .> factorize0 E' e')).
        apply H4. rewrite eq'. cat.
        rewrite comp_assoc, eq. reflexivity.
      destruct (H2 E' (factorize0 E' e' .> e)). rewrite eq. auto.
        rewrite <- (H4 (factorize0 E' e' .> factorize' E e)).
        apply H4. rewrite eq. cat.
        rewrite comp_assoc, eq'. reflexivity.
    rewrite eq'. reflexivity.
    intros. destruct H3. apply unique'. rewrite H4. reflexivity.
Qed.

Theorem equalizer_skolem_iso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E E' : Ob C) (e : Hom E X) (e' : Hom E' X)
    (factorize : forall (E'' : Ob C) (e'' : Hom E'' X), Hom E'' E)
    (factorize' : forall (E'' : Ob C) (e'' : Hom E'' X), Hom E'' E'),
      equalizer_skolem C f g E e factorize ->
      equalizer_skolem C f g E' e' factorize' ->
      E ~ E'.
Proof.
  intros. edestruct equalizer_skolem_uiso.
    apply H.
    apply H0.
    do 2 destruct H1. eauto.
Qed.

Theorem coequalizer_skolem_uiso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (Q Q' : Ob C) (q : Hom Y Q) (q' : Hom Y Q')
  (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''), Hom Q Q'')
  (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''), Hom Q' Q''),
    coequalizer_skolem C f g Q q cofactorize ->
    coequalizer_skolem C f g Q' q' cofactorize' ->
    exists !! f : Hom Q Q', Iso f /\
      q .> f == q'.
Proof.
  unfold coequalizer_skolem; intros. destruct H, H0.
  destruct (H1 Q' q' H0) as [eq unique].
  destruct (H2 Q q H) as [eq' unique'].
  exists (cofactorize0 Q' q').
  repeat split.
    red. exists (cofactorize' Q q). split.
      destruct (H1 Q (q' .> cofactorize' Q q)). rewrite eq'. auto.
        rewrite <- (H4 (cofactorize0 Q' q' .> cofactorize' Q q)).
        apply H4. rewrite eq'. cat.
        rewrite <- comp_assoc, eq. reflexivity.
      destruct (H2 Q' (q .> cofactorize0 Q' q')). rewrite eq. auto.
        rewrite <- (H4 (cofactorize' Q q .> cofactorize0 Q' q')).
        apply H4. rewrite eq. cat.
        rewrite <- comp_assoc, eq'. reflexivity.
    rewrite eq. reflexivity.
    intros. destruct H3. apply unique. rewrite H4. reflexivity.
Qed.

Theorem coequalizer_skolem_iso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (Q Q' : Ob C) (q : Hom Y Q) (q' : Hom Y Q')
  (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''), Hom Q Q'')
  (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''), Hom Q' Q''),
    coequalizer_skolem C f g Q q cofactorize ->
    coequalizer_skolem C f g Q' q' cofactorize' ->
      Q ~ Q'.
Proof.
  intros. edestruct coequalizer_skolem_uiso.
    apply H.
    apply H0.
    do 2 destruct H1. eauto.
Qed.

(* TODO *) Theorem biequalizer_skolem_uiso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E : Ob C) (e : Hom E X) (q : Hom Y E)
    (factorize : forall (E'' : Ob C) (e'' : Hom E'' X), Hom E'' E)
    (cofactorize : forall (Q'' : Ob C) (q'' : Hom Y Q''), Hom E Q'')
    (E' : Ob C) (e' : Hom E' X) (q' : Hom Y E')
    (factorize' : forall (E'' : Ob C) (e'' : Hom E'' X), Hom E'' E')
    (cofactorize' : forall (Q'' : Ob C) (q'' : Hom Y Q''), Hom E' Q''),
      biequalizer_skolem C f g E e q factorize cofactorize ->
      biequalizer_skolem C f g E' e' q' factorize' cofactorize' ->
      exists !! f : Hom E E', Iso f /\
        e == f .> e' /\ q .> f == q'.
Proof.
  intros.
Abort.

Theorem equalizer_skolem_is_mono :
    forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), Hom E' E),
      equalizer_skolem C f g E e factorize -> Mon e.
Proof.
  unfold equalizer_skolem, setoid_unique, Mon. intros.
  rename X0 into Z. rename g0 into h'.
  destruct H as [eq H].
  destruct (H Z (h .> e)) as [u Hh].
    do 2 rewrite comp_assoc. rewrite eq. reflexivity.
  destruct (H Z (h' .> e)) as [u' Hh'].
    do 2 rewrite comp_assoc. rewrite eq. reflexivity.
  assert (factorize0 Z (h .> e) == factorize0 Z (h' .> e)).
    rewrite Hh, Hh'. reflexivity. reflexivity. assumption.
  specialize (Hh h); specialize (Hh' h').
  rewrite <- Hh, <- Hh'; try rewrite H1; reflexivity.
Defined.

Theorem equalizer_epi_is_iso
  : forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), Hom E' E),
      equalizer_skolem C f g E e factorize -> Epi e -> Iso e.
Proof.
  intros. assert (HMon : Mon e).
    eapply equalizer_skolem_is_mono; eauto.
    unfold Epi, equalizer_skolem, setoid_unique. intros.
    red. exists (factorize0 _ (id X)). split.
      edestruct H. specialize (H2 _ (id X)).
        assert (e .> factorize0 X (id X) .> e == id E .> e).
          destruct H2.
            cat.
            assocr. rewrite H2. cat. apply HMon. assumption.
      edestruct H. apply H2. cat.
Qed.

Theorem coequalizer_skolem_is_epi :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (Q : Ob C) (q : Hom Y Q)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), Hom Q Q'),
    coequalizer_skolem C f g Q q cofactorize -> Epi q.
Proof.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite <- dual_mon_epi.
  rewrite <- dual_equalizer_coequalizer_skolem in *.
  eapply equalizer_skolem_is_mono. eauto.
Qed.

Theorem coequalizer_mono_is_iso :
  forall (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (Q : Ob C) (q : Hom Y Q)
  (cofactorize : forall (Q' : Ob C) (q' : Hom Y Q'), Hom Q Q'),
    coequalizer_skolem C f g Q q cofactorize -> Mon q -> Iso q.
Proof.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite dual_mon_epi in H0.
  rewrite <- dual_iso_self.
  apply (equalizer_epi_is_iso (Dual C) Y X f g _ _ cofactorize0).
    rewrite dual_equalizer_coequalizer_skolem. exact H.
    exact H0.
Qed.

Theorem factorize_eq_mor :
  forall (C : Cat) (he : has_equalizers C) (X Y : Ob C) (f g : Hom X Y),
    factorize f g _ (eq_mor f g) == id (eq_ob f g).
Proof.
  intros. destruct he; simpl in *.
  edestruct is_equalizer0. apply H0; cat.
Defined.

Theorem cofactorize_eq_mor :
  forall (C : Cat) (he : has_coequalizers C) (X Y : Ob C) (f g : Hom X Y),
    cofactorize f g _ (coeq_mor f g) == id (coeq_ob f g).
Proof.
  intros. destruct he; simpl in *.
  edestruct is_coequalizer0. apply H0; cat.
Defined.



(* TODO : Dual instances *)