Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Cat.

Set Implicit Arguments.

Definition pullback_skolem
  (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (factor : forall {P' : Ob C} (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P)
  : Prop := p1 .> f == p2 .> g /\
    forall (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y),
      setoid_unique (fun u : Hom Q P => u .> p1 == q1 /\ u .> p2 == q2) (factor q1 q2).

Definition pushout_skolem
  (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (e : forall (P' : Ob C) (p1' : Hom X P') (p2' : Hom Y P'), Hom P P')
  : Prop := f .> p1 == g .> p2 /\
    forall (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q),
      setoid_unique (fun u : Hom P Q => p1 .> u == q1 /\ p2 .> u == q2) (e Q q1 q2).

Class has_pullbacks (C : Cat) : Type :=
{
    pullbackOb : forall {X Y A : Ob C}, Hom X A -> Hom Y A -> Ob C;
    pullbackObProper : forall (X Y A : Ob C) (f f' : Hom X A)
      (g g' : Hom Y A), f == f' -> g == g' ->
        JMequiv (id (pullbackOb f g)) (id (pullbackOb f' g'));
    pull1 : forall {X Y A : Ob C} (f : Hom X A) (g : Hom Y A),
      Hom (pullbackOb f g) X;
    pull2 : forall {X Y A : Ob C} (f : Hom X A) (g : Hom Y A),
      Hom (pullbackOb f g) Y;
    pull1_Proper : forall (X Y A : Ob C) (f f' : Hom X A) (g g' : Hom Y A),
      f == f' -> g == g' -> JMequiv (pull1 f g) (pull1 f' g');
    pull2_Proper : forall (X Y A : Ob C) (f f' : Hom X A) (g g' : Hom Y A),
      f == f' -> g == g' -> JMequiv (pull2 f g) (pull2 f' g');
    factor : forall {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
      {P : Ob C} (p1 : Hom P X) (p2 : Hom P Y), Hom P (pullbackOb f g);
    is_pullback : forall (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
      pullback_skolem C f g (pullbackOb f g) (pull1 f g) (pull2 f g)
        (@factor X Y A f g)
}.

Class has_pushouts (C : Cat) : Type :=
{
    pushoutOb : forall {X Y A : Ob C}, Hom A X -> Hom A Y -> Ob C;
    pushoutObProper : forall (X Y A : Ob C) (f f' : Hom A X)
      (g g' : Hom A Y), f == f' -> g == g' ->
        JMequiv (id (pushoutOb f g)) (id (pushoutOb f' g'));
    push1 : forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y),
      Hom X (pushoutOb f g);
    push2 : forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y),
      Hom Y (pushoutOb f g);
    push1_Proper : forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (push1 f g) (push1 f' g');
    push2_Proper : forall (X Y A : Ob C) (f f' : Hom A X) (g g' : Hom A Y),
      f == f' -> g == g' -> JMequiv (push2 f g) (push2 f' g');
    cofactor : forall {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
      {P : Ob C} (p1 : Hom X P) (p2 : Hom Y P), Hom (pushoutOb f g) P;
    is_pushout : forall (X Y A : Ob C) (f : Hom A X) (g : Hom A Y),
      pushout_skolem C f g (pushoutOb f g) (push1 f g) (push2 f g)
        (@cofactor X Y A f g)
}.

Theorem dual_pullback_pushout :
  forall (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (factor : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P),
    pullback_skolem C f g P p1 p2 factor <->
    pushout_skolem (Dual C) f g P p1 p2 factor.
Proof. cat. Qed.

Theorem pullback_skolem_uiso :
  forall (C : Cat) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (factor : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P)
  (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y)
  (factor' : forall (Q' : Ob C) (q1' : Hom Q' X) (q2' : Hom Q' Y), Hom Q' Q),
    pullback_skolem C f g P p1 p2 factor ->
    pullback_skolem C f g Q q1 q2 factor' ->
    exists!! f : Hom P Q, Iso f /\
      f .> q1 == p1 /\ f .> q2 == p2.
Proof.
  intros. destruct H as [HP HP'], H0 as [HQ HQ'].
  exists (factor' P p1 p2).
  destruct
    (HP' P p1 p2) as [[HP1 HP2] HP3],
    (HP' Q q1 q2) as [[HP1' HP2'] HP3'],
    (HQ' P p1 p2) as [[HQ1' HQ2'] HQ3'],
    (HQ' Q q1 q2) as [[HQ1 HQ2] HQ3].
  repeat split; cat.
    red. exists (factor0 Q q1 q2). split.
      rewrite <- (HP3 (factor' P p1 p2 .> factor0 Q q1 q2)); auto.
        assocr'. rewrite HP1', HQ1', HP2', HQ2'. cat.
      rewrite <- (HQ3 (factor0 Q q1 q2 .> factor' P p1 p2)); auto.
        assocr'. rewrite HQ2', HQ1', HP2', HP1'. cat.
Qed.

Theorem pullback_skolem_iso :
  forall (C : Cat) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (e : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P)
  (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y)
  (e' : forall (Q' : Ob C) (q1' : Hom Q' X) (q2' : Hom Q' Y), Hom Q' Q),
    pullback_skolem C f g P p1 p2 e ->
    pullback_skolem C f g Q q1 q2 e' ->
    P ~ Q.
Proof.
  intros. destruct (pullback_skolem_uiso H H0).
  red. exists x. destruct H1 as [[H1 _] _]. assumption.
Qed.

Theorem pushout_uiso :
  forall (C : Cat) (X Y A : Ob C) (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (cofactor : forall (P' : Ob C) (p1' : Hom X P') (p2 : Hom Y P'), Hom P P')
  (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q)
  (cofactor' : forall (Q' : Ob C) (q1' : Hom X Q') (q2' : Hom Y Q'), Hom Q Q'),
    pushout_skolem C f g P p1 p2 cofactor ->
    pushout_skolem C f g Q q1 q2 cofactor' ->
    exists!! f : Hom Q P, Iso f /\
        p1 == q1 .> f /\ p2 == q2 .> f.
      (*exists!! f : Hom P Q, Iso f /\
        p1 .> f == q1 /\ p2 .> f == q2.*)
Proof.
  intro. rewrite <- (dual_involution_axiom C). intros.
  rewrite <- dual_pullback_pushout in H.
  rewrite <- dual_pullback_pushout in H0.
  destruct (pullback_skolem_uiso H H0). simpl in *.
  exists x. cat.
    rewrite dual_iso_self. assumption.
    symmetry. assumption.
    symmetry. assumption.
    apply H2. cat.
      rewrite dual_iso_self. assumption.
        symmetry. assumption.
        symmetry. assumption.
Qed.

Theorem pushout_iso :
  forall (C : Cat) (X Y A : Ob C) (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (cofactor : forall (P' : Ob C) (p1' : Hom X P') (p2 : Hom Y P'), Hom P P')
  (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q)
  (cofactor' : forall (Q' : Ob C) (q1' : Hom X Q') (q2' : Hom Y Q'), Hom Q Q'),
    pushout_skolem C f g P p1 p2 cofactor ->
    pushout_skolem C f g Q q1 q2 cofactor' ->
    P ~ Q.
Proof.
  intros. destruct (pushout_uiso H H0).
  symmetry. cat.
Qed.

Print Assumptions pushout_iso.