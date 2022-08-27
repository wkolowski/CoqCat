From Cat Require Import Cat.
From Cat.Limits Require Import Initial Terminal Product Coproduct Equalizer.

Set Implicit Arguments.

Definition isPullback
  (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (pullL : Hom P X) (pullR : Hom P Y)
  (factor : forall {P' : Ob C} (pullL' : Hom P' X) (pullR' : Hom P' Y),
              pullL' .> f == pullR' .> g -> Hom P' P)
  : Prop :=
    pullL .> f == pullR .> g
      /\
    forall (Q : Ob C) (pullL2 : Hom Q X) (pullR2 : Hom Q Y) (H : pullL2 .> f == pullR2 .> g),
      setoid_unique (fun u : Hom Q P => u .> pullL == pullL2 /\ u .> pullR == pullR2) (factor pullL2 pullR2 H).

Class HasPullbacks (C : Cat) : Type :=
{
  pullback : forall {X Y A : Ob C}, Hom X A -> Hom Y A -> Ob C;
  pullbackProper :
    forall (X Y A : Ob C) (f f' : Hom X A) (g g' : Hom Y A),
      f == f' -> g == g' -> JMequiv (id (pullback f g)) (id (pullback f' g'));
  pullL : forall {X Y A : Ob C} (f : Hom X A) (g : Hom Y A), Hom (pullback f g) X;
  pullR : forall {X Y A : Ob C} (f : Hom X A) (g : Hom Y A), Hom (pullback f g) Y;
  Proper_pullL :
    forall (X Y A : Ob C) (f f' : Hom X A) (g g' : Hom Y A),
      f == f' -> g == g' -> JMequiv (pullL f g) (pullL f' g');
  Proper_pullR :
    forall (X Y A : Ob C) (f f' : Hom X A) (g g' : Hom Y A),
      f == f' -> g == g' -> JMequiv (pullR f g) (pullR f' g');
  factor :
    forall {X Y A : Ob C} (f : Hom X A) (g : Hom Y A) {P : Ob C} (pullL : Hom P X) (pullR : Hom P Y),
      pullL .> f == pullR .> g -> Hom P (pullback f g);
  is_pullback :
    forall (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
      isPullback C f g (pullback f g) (pullL f g) (pullR f g) (@factor X Y A f g)
}.

Arguments pullback [C _ X Y A] _ _.
Arguments pullL      [C _ X Y A] _ _.
Arguments pullR      [C _ X Y A] _ _.
Arguments factor     [C _ X Y A f g P pullL pullR] _.

Lemma isPullback_uiso :
  forall
    (C : Cat) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A)
    (P1 : Ob C) (pullL1 : Hom P1 X) (pullR1 : Hom P1 Y)
    (factor1 : forall (P1' : Ob C) (pullL1' : Hom P1' X) (pullR1' : Hom P1' Y),
                 pullL1' .> f == pullR1' .> g -> Hom P1' P1)
    (P2 : Ob C) (pullL2 : Hom P2 X) (pullR2 : Hom P2 Y)
    (factor2 : forall (P2' : Ob C) (pullL2' : Hom P2' X) (pullR2' : Hom P2' Y),
                 pullL2' .> f == pullR2' .> g -> Hom P2' P2),
      isPullback C f g P1 pullL1 pullR1 factor1 ->
      isPullback C f g P2 pullL2 pullR2 factor2 ->
        exists!! f : Hom P1 P2, isIso f /\ f .> pullL2 == pullL1 /\ f .> pullR2 == pullR1.
Proof.
  intros. destruct H as [HP1 HP1'], H0 as [HP2 HP2'].
  exists (factor2 P1 pullL1 pullR1 HP1).
  destruct
    (HP1' P1 pullL1 pullR1 HP1) as [[HP11 HP12] HP13],
    (HP1' P2 pullL2 pullR2 HP2) as [[HP11' HP12'] HP13'],
    (HP2' P1 pullL1 pullR1 HP1) as [[HP21' HP22'] HP23'],
    (HP2' P2 pullL2 pullR2 HP2) as [[HP21 HP22] HP23].
  repeat split; cat.
    red. exists (factor1 P2 pullL2 pullR2 HP2). split.
      rewrite <- (HP13 (factor2 P1 pullL1 pullR1 HP1 .> factor1 P2 pullL2 pullR2 HP2)); auto.
        assocr'. rewrite HP11', HP21', HP12', HP22'. cat.
      rewrite <- (HP23 (factor1 P2 pullL2 pullR2 HP2 .> factor2 P1 pullL1 pullR1 HP1)); auto.
        assocr'. rewrite HP22', HP21', HP12', HP11'. cat.
Qed.

Lemma isPullback_iso :
  forall
    (C : Cat) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A)
    (P1 : Ob C) (pullL1 : Hom P1 X) (pullR1 : Hom P1 Y)
    (factor1 : forall (P1' : Ob C) (pullL1' : Hom P1' X) (pullR1' : Hom P1' Y),
                 pullL1' .> f == pullR1' .> g -> Hom P1' P1)
    (P2 : Ob C) (pullL2 : Hom P2 X) (pullR2 : Hom P2 Y)
    (factor2 : forall (P2' : Ob C) (pullL2' : Hom P2' X) (pullR2' : Hom P2' Y),
                 pullL2' .> f == pullR2' .> g -> Hom P2' P2),
      isPullback C f g P1 pullL1 pullR1 factor1 ->
      isPullback C f g P2 pullL2 pullR2 factor2 ->
        P1 ~ P2.
Proof.
  intros. destruct (isPullback_uiso H H0).
  red. exists x. destruct H1 as [[H1 _] _]. assumption.
Qed.

Lemma isProduct_isPullback :
  forall
    (C : Cat) (ht : HasTerm C) (X Y : Ob C)
    (P : Ob C) (pullL : Hom P X) (pullR : Hom P Y)
    (fpair : forall (P' : Ob C) (pullL' : Hom P' X) (pullR' : Hom P' Y), Hom P' P),
      isPullback C (delete X) (delete Y) P pullL pullR
        (fun (P' : Ob C) (pullL' : Hom P' X) (pullR' : Hom P' Y)
             (H : pullL' .> delete X == pullR' .> delete Y) => fpair P' pullL' pullR') ->
        isProduct C P pullL pullR fpair.
Proof.
  red; intros. edestruct H, (H1 _ f g) as [[H2 H3] H4].
    term.
    repeat split.
      rewrite H2. reflexivity.
      rewrite H3. reflexivity.
      intros. apply H4. cat; [rewrite H5 | rewrite H6]; reflexivity.
Qed.

Lemma isPullback_isProduct :
  forall
    (C : Cat) (ht : HasTerm C) (X Y : Ob C)
    (P : Ob C) (pullL : Hom P X) (pullR : Hom P Y)
    (fpair : forall (P' : Ob C) (f : Hom P' X) (g : Hom P' Y), Hom P' P),
      isProduct C P pullL pullR fpair ->
        isPullback C
          (delete X) (delete Y) P pullL pullR (fun (P' : Ob C)
          (pullL' : Hom P' X) (pullR' : Hom P' Y) _ => fpair P' pullL' pullR').
Proof.
  red; intros. repeat split.
    term.
    edestruct H, H1. rewrite <- H3. reflexivity.
    edestruct H, H1. rewrite <- H4. reflexivity.
    intros. edestruct H. apply H3. cat.
      rewrite H1. reflexivity.
      rewrite H5. reflexivity.
Qed.

Lemma isEqualizer_isPullback
  (C : Cat) (X Y : Ob C) (f g : Hom X Y)
  (P : Ob C) (p : Hom P X) (factor : forall (P' : Ob C) (f : Hom P' X) (g : Hom P' X), Hom P' P) :
    isPullback C f g P p p (fun P' pullL' pullR' _ => factor P' pullL' pullR') ->
      isEqualizer C f g P p (fun (P' : Ob C) (p : Hom P' X) _ => factor P' p p).
Proof.
  repeat split.
    destruct H. assumption.
    edestruct H, (H2 _ _ _ H0), H3. assumption.
    intros. edestruct H, (H3 _ _ _ H0). apply H5. cat.
Qed.

(* TODO : finish *) (*Lemma isPullback_isEqualizer :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C) (f g : Hom X Y)
  (E : Ob C) (e1 : Hom E X) (e2 : Hom E X)
  (factorize : forall (E' : Ob C) (e : Hom E' X),
    e .> f == e .> g -> Hom E' E),
    isEqualizer C f g E e1 factorize ->
    isEqualizer C f g E e2 factorize ->
    isPullback C f g (product E E) (outl .> e1) (outr .> e2)
      (fun (E' : Ob C) (e1 : Hom E' X) (e2 : Hom E' X) _ =>
        fpair (factorize E' e1) (factorize E' e2)).
Proof.
  intros. pose (eq := isEqualizer_equiv H H0).
  repeat split.
    rewrite eq. edestruct H0. assocr'. rewrite e.
      f_equiv. destruct hp. cbn in *. do 2 red in is_product.
Abort.*)

(* 
https://math.stackexchange.com/questions/308391/products-and-pullbacks-imply-equalizers

Zhen Lin *)