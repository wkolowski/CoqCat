From Cat Require Import Cat.
From Cat.Limits Require Import Initial Terminal Product Coproduct Equalizer Coequalizer Pullback.

Set Implicit Arguments.

Definition isPushout
  (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (pushl : Hom X P) (pushr : Hom Y P)
  (cofactor : forall {P' : Ob C} (x : Hom X P') (y : Hom Y P'), f .> x == g .> y -> Hom P P')
  : Prop :=
    f .> pushl == g .> pushr
      /\
    forall (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q) (H : f .> q1 == g .> q2),
      setoid_unique (fun u : Hom P Q => pushl .> u == q1 /\ pushr .> u == q2) (cofactor q1 q2 H).

Class HasPushouts (C : Cat) : Type :=
{
  pushout : forall {X Y A : Ob C}, Hom A X -> Hom A Y -> Ob C;
  pushoutProper :
    forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (id (pushout f g)) (id (pushout f' g'));
  pushl : forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y), Hom X (pushout f g);
  pushr : forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y), Hom Y (pushout f g);
  Proper_pushl :
    forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (pushl f g) (pushl f' g');
  Proper_pushr :
    forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (pushr f g) (pushr f' g');
  cofactor :
    forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y) {P : Ob C} (pushl : Hom X P) (pushr : Hom Y P),
      f .> pushl == g .> pushr -> Hom (pushout f g) P;
  is_pushout :
    forall (X Y A : Ob C) (f : Hom A X) (g : Hom A Y),
      isPushout C f g (pushout f g) (pushl f g) (pushr f g) (@cofactor X Y A f g)
}.

Arguments pushout [C _ X Y A] _ _.
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