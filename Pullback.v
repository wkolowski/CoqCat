Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.

Definition pullback (C : Cat) {A B X : Ob C} (f : Hom A X) (g : Hom B X)
  (P : Ob C) (pA : Hom P A) (pB : Hom P B) := forall (Q : Ob C) (qA : Hom Q A)
    (qB : Hom Q B), exists!! u : Hom Q P, qA == u .> pA /\ qB == u .> pB.

Definition pullback_skolem
  (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (factor : forall {P' : Ob C} (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P)
  : Prop := p1 .> f == p2 .> g /\
    forall (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y),
      setoid_unique (fun u : Hom Q P => q1 .> f == q2 .> g) (factor q1 q2).

Definition pushout_skolem
  (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (e : forall (P' : Ob C) (p1' : Hom X P') (p2' : Hom Y P'), Hom P P')
  : Prop := f .> p1 == g .> p2 /\
    forall (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q),
      setoid_unique (fun u : Hom P Q => f .> q1 == g .> q2) (e Q q1 q2).

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

Theorem pullback_iso : forall (C : Cat) (A B X P Q : Ob C)
    (f : Hom A X) (g : Hom B X) (pA : Hom P A) (pB : Hom P B) (qA : Hom Q A)
    (qB : Hom Q B), pullback C f g P pA pB -> pullback C f g Q qA qB -> P ~ Q.
Proof.
  unfold pullback, isomorphic, Iso; intros.
  destruct (H0 P pA pB) as [u1 [[u1_eq1 u1_eq2] uniq1]],
(H Q qA qB) as [u2 [[u2_eq1 u2_eq2] uniq2]].
  exists u1, u2; split.
    destruct (H P pA pB) as (i, [[i_iso1 i_iso2] uq]).
      assert (i_is_id : i == id P). apply uq; cat.
      rewrite <- i_is_id. symmetry. apply uq. split.
        cat. rewrite <- u2_eq1. assumption.
        cat. rewrite <- u2_eq2. assumption.
    destruct (H0 Q qA qB) as (i, [[i_iso1 i_iso2] uq]).
      assert (i_is_id : i == id Q). apply uq; cat.
      rewrite <- i_is_id. symmetry. apply uq. split.
        cat. rewrite <- u1_eq1. assumption.
        cat. rewrite <- u1_eq2. assumption.
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
  intros. destruct H as [Heq Hpull], H0 as [Heq' Hpull'].
  red. exists (e' P p1 p2).
  red. exists (e Q q1 q2).
  split.
    destruct (Hpull P p1 p2). specialize (H0 (e' P p1 p2 .> e Q q1 q2) H).
      rewrite <- H0. destruct (Hpull P p1 p2). apply H2. assumption.
    destruct (Hpull' Q q1 q2). specialize (H0 (e Q q1 q2 .> e' P p1 p2) H).
      rewrite <- H0. destruct (Hpull' Q q1 q2). apply H2. assumption.
Qed.

Theorem dual_pullback_pushout :
  forall (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (factor : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P),
    pullback_skolem C f g P p1 p2 factor <->
    pushout_skolem (Dual C) f g P p1 p2 factor.
Proof. cat. Qed.


  
