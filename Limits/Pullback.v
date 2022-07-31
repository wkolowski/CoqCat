From Cat Require Import Cat.
From Cat.Limits Require Import InitTerm ProdCoprod Equalizer.

Set Implicit Arguments.

Definition pullback
  (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (factor : forall {P' : Ob C} (p1' : Hom P' X) (p2' : Hom P' Y), p1' .> f == p2' .> g -> Hom P' P)
  : Prop :=
    p1 .> f == p2 .> g
      /\
    forall (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y) (H : q1 .> f == q2 .> g),
      setoid_unique (fun u : Hom Q P => u .> p1 == q1 /\ u .> p2 == q2) (factor q1 q2 H).

Definition pushout
  (C : Cat) {X Y A : Ob C} (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (cofactor : forall {P' : Ob C} (p1' : Hom X P') (p2' : Hom Y P'), f .> p1' == g .> p2' -> Hom P P')
  : Prop :=
    f .> p1 == g .> p2
      /\
    forall (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q) (H : f .> q1 == g .> q2),
      setoid_unique (fun u : Hom P Q => p1 .> u == q1 /\ p2 .> u == q2) (cofactor q1 q2 H).

Class HasPullbacks (C : Cat) : Type :=
{
  pullbackOb : forall {X Y A : Ob C}, Hom X A -> Hom Y A -> Ob C;
  pullbackObProper :
    forall (X Y A : Ob C) (f f' : Hom X A) (g g' : Hom Y A),
      f == f' -> g == g' -> JMequiv (id (pullbackOb f g)) (id (pullbackOb f' g'));
  pull1 : forall {X Y A : Ob C} (f : Hom X A) (g : Hom Y A), Hom (pullbackOb f g) X;
  pull2 : forall {X Y A : Ob C} (f : Hom X A) (g : Hom Y A), Hom (pullbackOb f g) Y;
  Proper_pull1 :
    forall (X Y A : Ob C) (f f' : Hom X A) (g g' : Hom Y A),
      f == f' -> g == g' -> JMequiv (pull1 f g) (pull1 f' g');
  Proper_pull2 :
    forall (X Y A : Ob C) (f f' : Hom X A) (g g' : Hom Y A),
      f == f' -> g == g' -> JMequiv (pull2 f g) (pull2 f' g');
  factor :
    forall {X Y A : Ob C} (f : Hom X A) (g : Hom Y A) {P : Ob C} (p1 : Hom P X) (p2 : Hom P Y),
      p1 .> f == p2 .> g -> Hom P (pullbackOb f g);
  is_pullback :
    forall (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
      pullback C f g (pullbackOb f g) (pull1 f g) (pull2 f g) (@factor X Y A f g)
}.

Arguments pullbackOb [C _ X Y A] _ _.
Arguments pull1      [C _ X Y A] _ _.
Arguments pull2      [C _ X Y A] _ _.
Arguments factor     [C _ X Y A f g P p1 p2] _.

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
      pushout C f g (pushoutOb f g) (push1 f g) (push2 f g) (@cofactor X Y A f g)
}.

Arguments pushoutOb [C _ X Y A] _ _.
Arguments push1     [C _ X Y A] _ _.
Arguments push2     [C _ X Y A] _ _.
Arguments cofactor  [C _ X Y A f g P p1 p2] _.

Lemma dual_pullback_pushout :
  forall
    (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (factor : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), p1' .> f == p2' .> g -> Hom P' P),
      pullback C f g P p1 p2 factor <-> pushout (Dual C) f g P p1 p2 factor.
Proof. cat. Defined.

Lemma pullback_uiso
  (C : Cat) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (factor : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), p1' .> f == p2' .> g -> Hom P' P)
  (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y)
  (factor' : forall (Q' : Ob C) (q1' : Hom Q' X) (q2' : Hom Q' Y), q1' .> f == q2' .> g -> Hom Q' Q) :
    pullback C f g P p1 p2 factor -> pullback C f g Q q1 q2 factor' ->
      exists!! f : Hom P Q, Iso f /\ f .> q1 == p1 /\ f .> q2 == p2.
Proof.
  intros. destruct H as [HP HP'], H0 as [HQ HQ'].
  exists (factor' P p1 p2 HP).
  destruct
    (HP' P p1 p2 HP) as [[HP1 HP2] HP3],
    (HP' Q q1 q2 HQ) as [[HP1' HP2'] HP3'],
    (HQ' P p1 p2 HP) as [[HQ1' HQ2'] HQ3'],
    (HQ' Q q1 q2 HQ) as [[HQ1 HQ2] HQ3].
  repeat split; cat.
    red. exists (factor Q q1 q2 HQ). split.
      rewrite <- (HP3 (factor' P p1 p2 HP .> factor Q q1 q2 HQ)); auto.
        assocr'. rewrite HP1', HQ1', HP2', HQ2'. cat.
      rewrite <- (HQ3 (factor Q q1 q2 HQ .> factor' P p1 p2 HP)); auto.
        assocr'. rewrite HQ2', HQ1', HP2', HP1'. cat.
Qed.

Lemma pullback_iso
  (C : Cat) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (factor : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), p1' .> f == p2' .> g -> Hom P' P)
  (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y)
  (factor' : forall (Q' : Ob C) (q1' : Hom Q' X) (q2' : Hom Q' Y), q1' .> f == q2' .> g -> Hom Q' Q) :
    pullback C f g P p1 p2 factor -> pullback C f g Q q1 q2 factor' -> P ~ Q.
Proof.
  intros. destruct (pullback_uiso H H0).
  red. exists x. destruct H1 as [[H1 _] _]. assumption.
Qed.

Lemma pushout_uiso
  (C : Cat) (X Y A : Ob C) (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (cofactor : forall (P' : Ob C) (p1' : Hom X P') (p2' : Hom Y P'),
    f .> p1' == g .> p2' -> Hom P P')
  (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q)
  (cofactor' : forall (Q' : Ob C) (q1' : Hom X Q') (q2' : Hom Y Q'),
    f .> q1' == g .> q2' -> Hom Q Q')
  : pushout C f g P p1 p2 cofactor -> pushout C f g Q q1 q2 cofactor' ->
      exists!! f : Hom Q P, Iso f /\ p1 == q1 .> f /\ p2 == q2 .> f.
Proof.
  revert X Y A f g P p1 p2 cofactor Q q1 q2 cofactor'.
  rewrite <- (Dual_Dual C). intros.
  rewrite <- dual_pullback_pushout in H.
  rewrite <- dual_pullback_pushout in H0.
  destruct (pullback_uiso H H0). cbn in *.
  exists x. cat.
    rewrite dual_iso_self. assumption.
    symmetry. assumption.
    symmetry. assumption.
    apply H2. cat.
      rewrite dual_iso_self. assumption.
        symmetry. assumption.
        symmetry. assumption.
Qed.

Lemma pushout_iso
  (C : Cat) (X Y A : Ob C) (f : Hom A X) (g : Hom A Y)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (cofactor : forall (P' : Ob C) (p1' : Hom X P') (p2' : Hom Y P'),
    f .> p1' == g .> p2' -> Hom P P')
  (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q)
  (cofactor' : forall (Q' : Ob C) (q1' : Hom X Q') (q2' : Hom Y Q'),
    f .> q1' == g .> q2' -> Hom Q Q')
  : pushout C f g P p1 p2 cofactor -> pushout C f g Q q1 q2 cofactor' -> P ~ Q.
Proof.
  intros. destruct (pushout_uiso H H0).
  symmetry. cat.
Qed.

Lemma pullback_product :
  forall
    (C : Cat) (ht : HasTerm C) (X Y : Ob C)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (fpair : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P),
      pullback C (delete X) (delete Y) P p1 p2
        (fun (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y)
             (H : p1' .> delete X == p2' .> delete Y) => fpair P' p1' p2') ->
        product C P p1 p2 fpair.
Proof.
  red; intros. edestruct H, (H1 _ f g) as [[H2 H3] H4].
    term.
    repeat split.
      rewrite H2. reflexivity.
      rewrite H3. reflexivity.
      intros. apply H4. cat; [rewrite H5 | rewrite H6]; reflexivity.
Qed.

Lemma product_pullback :
  forall
    (C : Cat) (ht : HasTerm C) (X Y : Ob C)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (fpair : forall (P' : Ob C) (f : Hom P' X) (g : Hom P' Y), Hom P' P),
      product C P p1 p2 fpair ->
        pullback C
          (delete X) (delete Y) P p1 p2 (fun (P' : Ob C)
          (p1' : Hom P' X) (p2' : Hom P' Y) _ => fpair P' p1' p2').
Proof.
  red; intros. repeat split.
    term.
    edestruct H, H1. rewrite <- H3. reflexivity.
    edestruct H, H1. rewrite <- H4. reflexivity.
    intros. edestruct H. apply H3. cat.
      rewrite H1. reflexivity.
      rewrite H5. reflexivity.
Qed.

Lemma pullback_equalizer
  (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (P : Ob C) (p : Hom P X) (factor : forall (P' : Ob C) (f : Hom P' X) (g : Hom P' X), Hom P' P) :
    pullback C f g P p p (fun P' p1' p2' _ => factor P' p1' p2') ->
      equalizer C f g P p (fun (P' : Ob C) (p : Hom P' X) _ => factor P' p p).
Proof.
  repeat split.
    destruct H. assumption.
    edestruct H, (H2 _ _ _ H0), H3. assumption.
    intros. edestruct H, (H3 _ _ _ H0). apply H5. cat.
Qed.

(* TODO : finish *) (*Lemma equalizer_pullback :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C) (f g : Hom X Y)
  (E : Ob C) (e1 : Hom E X) (e2 : Hom E X)
  (factorize : forall (E' : Ob C) (e : Hom E' X),
    e .> f == e .> g -> Hom E' E),
    equalizer C f g E e1 factorize ->
    equalizer C f g E e2 factorize ->
    pullback C f g (prodOb E E) (proj1 .> e1) (proj2 .> e2)
      (fun (E' : Ob C) (e1 : Hom E' X) (e2 : Hom E' X) _ =>
        fpair (factorize E' e1) (factorize E' e2)).
Proof.
  intros. pose (eq := equalizer_equiv H H0).
  repeat split.
    rewrite eq. edestruct H0. assocr'. rewrite e.
      f_equiv. destruct hp. cbn in *. do 2 red in is_product.
Abort.*)

(* 
https://math.stackexchange.com/questions/308391/products-and-pullbacks-imply-equalizers

Zhen Lin *)

Lemma pushout_coproduct :
  forall
    (C : Cat) (ht : HasInit C) (X Y : Ob C)
    (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (copair : forall (P' : Ob C) (f : Hom X P') (g : Hom Y P'), Hom P P'),
      pushout C (create X) (create Y) P p1 p2 (fun P' f g _ => copair P' f g) ->
        coproduct C P p1 p2 copair.
Proof.
  red; intros. edestruct H, (H1 _ f g) as [[H2 H3] H4].
    init.
    repeat split.
      rewrite H2. reflexivity.
      rewrite H3. reflexivity.
      intros. apply H4. cat; [rewrite H5 | rewrite H6]; reflexivity.
Qed.

Lemma coproduct_pushout :
  forall
    (C : Cat) (ht : HasInit C) (X Y : Ob C)
    (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (copair : forall (P' : Ob C) (f : Hom X P') (g : Hom Y P'), Hom P P'),
      coproduct C P p1 p2 copair ->
        pushout C (create X) (create Y) P p1 p2 (fun P' f g _ => copair P' f g).
Proof.
  red; intros. repeat split.
    init.
    edestruct H, H1. rewrite <- H3. reflexivity.
    edestruct H, H1. rewrite <- H4. reflexivity.
    intros. edestruct H. apply H3. cat.
      rewrite H1. reflexivity.
      rewrite H5. reflexivity.
Qed.

Lemma pushout_coequalizer :
  forall
    (C : Cat) (X Y : Ob C) (f g : Hom X Y)
    (P : Ob C) (p : Hom Y P)
    (cofactor : forall (P' : Ob C) (f : Hom Y P') (g : Hom Y P'), Hom P P'),
      pushout C f g P p p (fun P' f g _ => cofactor P' f g) ->
        coequalizer C f g P p (fun (P' : Ob C) (p : Hom Y P') _ => cofactor P' p p).
Proof.
  repeat split.
    destruct H. assumption.
    edestruct H, (H2 _ _ _ H0), H3. assumption.
    intros. edestruct H, (H3 _ _ _ H0). apply H5. cat.
Qed.