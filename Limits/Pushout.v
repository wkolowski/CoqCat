From Cat Require Import Cat.
From Cat.Limits Require Import Initial Terminal Product Coproduct Equalizer Coequalizer Pullback.

Set Implicit Arguments.

Definition isPushout
  (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (pushl : Hom X P) (pushr : Hom Y P)
  (cofactor : forall {P' : Ob C} (pushl' : Hom X P') (pushr' : Hom Y P'),
                f .> pushl' == g .> pushr' -> Hom P P')
  : Prop :=
    f .> pushl == g .> pushr
      /\
    forall (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q) (H : f .> q1 == g .> q2),
      setoid_unique (fun u : Hom P Q => pushl .> u == q1 /\ pushr .> u == q2) (cofactor q1 q2 H).

Class isPushout'
  (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (pushl : Hom X P) (pushr : Hom Y P)
  (cofactor : forall {P' : Ob C} (pushl' : Hom X P') (pushr' : Hom Y P'),
                f .> pushl' == g .> pushr' -> Hom P P')
  : Prop :=
{
  oks : f .> pushl == g .> pushr;
  universal :
    forall (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q) (H : f .> q1 == g .> q2) (h : Hom P Q),
      cofactor q1 q2 H == h <-> pushl .> h == q1 /\ pushr .> h == q2
}.

Class isPushout''
  (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (pushl : Hom X P) (pushr : Hom Y P)
  (cofactor : forall {P' : Ob C} (pushl' : Hom X P') (pushr' : Hom Y P'),
                f .> pushl' == g .> pushr' -> Hom P P')
  : Prop :=
{
  oks' : f .> pushl == g .> pushr;
  pushl_cofactor :
    forall (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q) (H : f .> q1 == g .> q2),
      pushl .> cofactor q1 q2 H == q1;
  pushr_cofactor :
    forall (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q) (H : f .> q1 == g .> q2),
      pushr .> cofactor q1 q2 H == q2;
  pushout_equiv :
    forall (Q : Ob C) (h1 h2 : Hom P Q),
      pushl .> h1 == pushl .> h2 -> pushr .> h1 == pushr .> h2 -> h1 == h2
}.

Lemma isPushout_isPusohut'' :
  forall
    (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
    (P : Ob C) (pushl : Hom X P) (pushr : Hom Y P)
    (cofactor : forall {P' : Ob C} (pushl' : Hom X P') (pushr' : Hom Y P'),
                  f .> pushl' == g .> pushr' -> Hom P P'),
      isPushout C f g P pushl pushr (@cofactor) <-> isPushout'' C f g P pushl pushr (@cofactor).
Proof.
  split.
  - split.
    + apply H.
    + apply H.
    + apply H.
    + intros. etransitivity.
      symmetry; apply H. Unshelve.
      * split; eassumption.
      * apply H. split; reflexivity.
      * rewrite <- !comp_assoc. f_equiv. apply H.
  - split.
    + apply oks'.
    + split.
      * split.
        -- apply pushl_cofactor.
        -- apply pushr_cofactor.
      * intros y []. symmetry; apply pushout_equiv.
        -- rewrite pushl_cofactor; assumption.
        -- rewrite pushr_cofactor; assumption.
Qed.

Lemma isPushout'_isPusohut'' :
  forall
    (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
    (P : Ob C) (pushl : Hom X P) (pushr : Hom Y P)
    (cofactor : forall {P' : Ob C} (pushl' : Hom X P') (pushr' : Hom Y P'),
                  f .> pushl' == g .> pushr' -> Hom P P'),
      isPushout' C f g P pushl pushr (@cofactor) <-> isPushout'' C f g P pushl pushr (@cofactor).
Proof.
  split.
  - split.
    + apply oks.
    + intros.
      destruct (universal _ _ _ H0 (cofactor Q q1 q2 H0)) as [[-> _] _]; reflexivity.
    + intros.
      destruct (universal _ _ _ H0 (cofactor Q q1 q2 H0)) as [[_ ->] _]; reflexivity.
    + intros * H1 H2. etransitivity; cycle 1.
      * rewrite universal; [cat |].
        rewrite <- comp_assoc, oks, comp_assoc; reflexivity.
      * symmetry; apply universal. split; assumption.
  - split.
    + apply oks'.
    + split.
      * intros <-. split.
        -- apply pushl_cofactor.
        -- apply pushr_cofactor.
      * intros [H1 H2].
        symmetry; apply pushout_equiv.
        -- rewrite pushl_cofactor; assumption.
        -- rewrite pushr_cofactor; assumption.
Qed.

Class HasPushouts (C : Cat) : Type :=
{
  pushoutOb : forall {X Y A : Ob C}, Hom A X -> Hom A Y -> Ob C;
  pushoutObProper :
    forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (id (pushoutOb f g)) (id (pushoutOb f' g'));
  pushl : forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y), Hom X (pushoutOb f g);
  pushr : forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y), Hom Y (pushoutOb f g);
  Proper_pushl :
    forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (pushl f g) (pushl f' g');
  Proper_pushr :
    forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (pushr f g) (pushr f' g');
  cofactor :
    forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y) {P : Ob C} (pushl : Hom X P) (pushr : Hom Y P),
      f .> pushl == g .> pushr -> Hom (pushoutOb f g) P;
  is_pushout :
    forall (X Y A : Ob C) (f : Hom A X) (g : Hom A Y),
      isPushout C f g (pushoutOb f g) (pushl f g) (pushr f g) (@cofactor X Y A f g)
}.

Arguments pushoutOb [C _ X Y A] _ _.
Arguments pushl     [C _ X Y A] _ _.
Arguments pushr     [C _ X Y A] _ _.
Arguments cofactor  [C _ X Y A f g P pushl pushr] _.

Lemma isPullback_Dual :
  forall
    (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
    (P : Ob C) (pushl : Hom X P) (pushr : Hom Y P)
    (cofactor : forall (P' : Ob C) (pushl' : Hom X P') (pushr' : Hom Y P'),
                  f .> pushl' == g .> pushr' -> Hom P P'),
      isPullback (Dual C) f g P pushl pushr cofactor
        =
      isPushout C f g P pushl pushr cofactor.
Proof. reflexivity. Defined.

Lemma isPushout_Dual :
  forall
    (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
    (P : Ob C) (pushl : Hom P X) (pushr : Hom P Y)
    (factor : forall (P' : Ob C) (pushl' : Hom P' X) (pushr' : Hom P' Y),
                pushl' .> f == pushr' .> g -> Hom P' P),
      isPushout (Dual C) f g P pushl pushr factor
        =
      isPullback C f g P pushl pushr factor.
Proof. reflexivity. Defined.

Lemma isPushout_uiso :
  forall
    (C : Cat) (X Y A : Ob C) (f : Hom A X) (g : Hom A Y)
    (P1 : Ob C) (pushl1 : Hom X P1) (pushr1 : Hom Y P1)
    (cofactor1 : forall (P1' : Ob C) (pushl1' : Hom X P1') (pushr1' : Hom Y P1'),
                   f .> pushl1' == g .> pushr1' -> Hom P1 P1')
    (P2 : Ob C) (pushl2 : Hom X P2) (pushr2 : Hom Y P2)
    (cofactor2 : forall (P2' : Ob C) (pushl2' : Hom X P2') (pushr2' : Hom Y P2'),
                   f .> pushl2' == g .> pushr2' -> Hom P2 P2'),
      isPushout C f g P1 pushl1 pushr1 cofactor1 ->
      isPushout C f g P2 pushl2 pushr2 cofactor2 ->
        exists!! f : Hom P2 P1, isIso f /\ pushl1 == pushl2 .> f /\ pushr1 == pushr2 .> f.
Proof.
  intros C; rewrite <- (Dual_Dual C); intros.
  rewrite isPushout_Dual in *.
  destruct (isPullback_uiso H H0). cbn in *.
  exists x. cat.
    rewrite isIso_Dual. assumption.
    symmetry. assumption.
    symmetry. assumption.
    apply H2. cat.
      rewrite isIso_Dual. assumption.
        symmetry. assumption.
        symmetry. assumption.
Qed.

Lemma isPushout_iso :
  forall
    (C : Cat) (X Y A : Ob C) (f : Hom A X) (g : Hom A Y)
    (P1 : Ob C) (pushl1 : Hom X P1) (pushr1 : Hom Y P1)
    (cofactor1 : forall (P1' : Ob C) (pushl1' : Hom X P1') (pushr1' : Hom Y P1'),
                   f .> pushl1' == g .> pushr1' -> Hom P1 P1')
    (P2 : Ob C) (pushl2 : Hom X P2) (pushr2 : Hom Y P2)
    (cofactor2 : forall (P2' : Ob C) (pushl2' : Hom X P2') (pushr2' : Hom Y P2'),
                   f .> pushl2' == g .> pushr2' -> Hom P2 P2'),
      isPushout C f g P1 pushl1 pushr1 cofactor1 ->
      isPushout C f g P2 pushl2 pushr2 cofactor2 ->
        P1 ~ P2.
Proof.
  intros. destruct (isPushout_uiso H H0).
  symmetry. cat.
Qed.

Lemma isCoproduct_isPushout :
  forall
    (C : Cat) (ht : HasInit C) (X Y : Ob C)
    (P : Ob C) (pushl : Hom X P) (pushr : Hom Y P)
    (copair : forall (P' : Ob C) (f : Hom X P') (g : Hom Y P'), Hom P P'),
      isPushout C (create X) (create Y) P pushl pushr (fun P' f g _ => copair P' f g) ->
        isCoproduct C P pushl pushr copair.
Proof.
  red; intros. edestruct H, (H1 _ f g) as [[H2 H3] H4].
    init.
    repeat split.
      rewrite H2. reflexivity.
      rewrite H3. reflexivity.
      intros. apply H4. cat; [rewrite H5 | rewrite H6]; reflexivity.
Qed.

Lemma isPushout_isCoproduct :
  forall
    (C : Cat) (ht : HasInit C) (X Y : Ob C)
    (P : Ob C) (pushl : Hom X P) (pushr : Hom Y P)
    (copair : forall (P' : Ob C) (f : Hom X P') (g : Hom Y P'), Hom P P'),
      isCoproduct C P pushl pushr copair ->
        isPushout C (create X) (create Y) P pushl pushr (fun P' f g _ => copair P' f g).
Proof.
  red; intros. repeat split.
    init.
    edestruct H, H1. rewrite <- H3. reflexivity.
    edestruct H, H1. rewrite <- H4. reflexivity.
    intros. edestruct H. apply H3. cat.
      rewrite H1. reflexivity.
      rewrite H5. reflexivity.
Qed.

Lemma isCoequalizer_isPushout :
  forall
    (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (P : Ob C) (p : Hom Y P)
    (cofactor : forall (P' : Ob C) (f : Hom Y P') (g : Hom Y P'), Hom P P'),
      isPushout C f g P p p (fun P' f g _ => cofactor P' f g) ->
        isCoequalizer C f g P p (fun (P' : Ob C) (p : Hom Y P') _ => cofactor P' p p).
Proof.
  repeat split.
    destruct H. assumption.
    edestruct H, (H2 _ _ _ H0), H3. assumption.
    intros. edestruct H, (H3 _ _ _ H0). apply H5. cat.
Qed.