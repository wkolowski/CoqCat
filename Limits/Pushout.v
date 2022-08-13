From Cat Require Import Cat.
From Cat.Limits Require Import Initial Terminal Product Coproduct Equalizer Coequalizer Pullback.

Set Implicit Arguments.

Definition isPushout
  (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (cofactor : forall {P' : Ob C} (p1' : Hom X P') (p2' : Hom Y P'), f .> p1' == g .> p2' -> Hom P P')
  : Prop :=
    f .> p1 == g .> p2
      /\
    forall (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q) (H : f .> q1 == g .> q2),
      setoid_unique (fun u : Hom P Q => p1 .> u == q1 /\ p2 .> u == q2) (cofactor q1 q2 H).

Class HasPushouts (C : Cat) : Type :=
{
  pushoutOb : forall {X Y A : Ob C}, Hom A X -> Hom A Y -> Ob C;
  pushoutObProper :
    forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (id (pushoutOb f g)) (id (pushoutOb f' g'));
  push1 : forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y), Hom X (pushoutOb f g);
  push2 : forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y), Hom Y (pushoutOb f g);
  Proper_push1 :
    forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (push1 f g) (push1 f' g');
  Proper_push2 :
    forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (push2 f g) (push2 f' g');
  cofactor :
    forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y) {P : Ob C} (p1 : Hom X P) (p2 : Hom Y P),
      f .> p1 == g .> p2 -> Hom (pushoutOb f g) P;
  is_pushout :
    forall (X Y A : Ob C) (f : Hom A X) (g : Hom A Y),
      isPushout C f g (pushoutOb f g) (push1 f g) (push2 f g) (@cofactor X Y A f g)
}.

Arguments pushoutOb [C _ X Y A] _ _.
Arguments push1     [C _ X Y A] _ _.
Arguments push2     [C _ X Y A] _ _.
Arguments cofactor  [C _ X Y A f g P p1 p2] _.

Lemma isPullback_Dual :
  forall
    (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
    (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (cofactor : forall (P' : Ob C) (p1' : Hom X P') (p2' : Hom Y P'), f .> p1' == g .> p2' -> Hom P P'),
      isPullback (Dual C) f g P p1 p2 cofactor
        =
      isPushout C f g P p1 p2 cofactor.
Proof. reflexivity. Defined.

Lemma isPushout_Dual :
  forall
    (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (factor : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), p1' .> f == p2' .> g -> Hom P' P),
      isPushout (Dual C) f g P p1 p2 factor
        =
      isPullback C f g P p1 p2 factor.
Proof. reflexivity. Defined.

Lemma isPushout_uiso
  (C : Cat) (X Y A : Ob C) (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (cofactor : forall (P' : Ob C) (p1' : Hom X P') (p2' : Hom Y P'),
    f .> p1' == g .> p2' -> Hom P P')
  (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q)
  (cofactor' : forall (Q' : Ob C) (q1' : Hom X Q') (q2' : Hom Y Q'),
    f .> q1' == g .> q2' -> Hom Q Q')
  : isPushout C f g P p1 p2 cofactor -> isPushout C f g Q q1 q2 cofactor' ->
      exists!! f : Hom Q P, isIso f /\ p1 == q1 .> f /\ p2 == q2 .> f.
Proof.
  revert X Y A f g P p1 p2 cofactor Q q1 q2 cofactor'.
  rewrite <- (Dual_Dual C). intros.
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

Lemma isPushout_iso
  (C : Cat) (X Y A : Ob C) (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (cofactor : forall (P' : Ob C) (p1' : Hom X P') (p2' : Hom Y P'),
    f .> p1' == g .> p2' -> Hom P P')
  (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q)
  (cofactor' : forall (Q' : Ob C) (q1' : Hom X Q') (q2' : Hom Y Q'),
    f .> q1' == g .> q2' -> Hom Q Q')
  : isPushout C f g P p1 p2 cofactor -> isPushout C f g Q q1 q2 cofactor' -> P ~ Q.
Proof.
  intros. destruct (isPushout_uiso H H0).
  symmetry. cat.
Qed.

Lemma isCoproduct_isPushout :
  forall
    (C : Cat) (ht : HasInit C) (X Y : Ob C)
    (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (copair : forall (P' : Ob C) (f : Hom X P') (g : Hom Y P'), Hom P P'),
      isPushout C (create X) (create Y) P p1 p2 (fun P' f g _ => copair P' f g) ->
        isCoproduct C P p1 p2 copair.
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
    (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (copair : forall (P' : Ob C) (f : Hom X P') (g : Hom Y P'), Hom P P'),
      isCoproduct C P p1 p2 copair ->
        isPushout C (create X) (create Y) P p1 p2 (fun P' f g _ => copair P' f g).
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