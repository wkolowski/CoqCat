From Cat Require Import Cat.
(* From Cat.Limits Require Import Equalizer. *)

Set Implicit Arguments.

Class isCoequalizer
  (C : Cat) {A B : Ob C} (f g : Hom A B)
  (Q : Ob C) (coequalize : Hom B Q)
  (cofactorize : forall {Q' : Ob C} {q : Hom B Q'}, f .> q == g .> q -> Hom Q Q')
  : Prop :=
{
  coequalize_ok : f .> coequalize == g .> coequalize;
  coequalize_cofactorize :
    forall {Q' : Ob C} {q : Hom B Q'} (H : f .> q == g .> q),
      coequalize .> cofactorize H == q;
  cofactorize_equiv :
    forall {Q' : Ob C} (h1 h2 : Hom Q Q'),
      coequalize .> h1 == coequalize .> h2 -> h1 == h2;
}.

#[export] Hint Mode isCoequalizer ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isCoequalizer ! ! ! - - - - - : core.

Section isCoequalizer.

Context
  {C : Cat} {A B : Ob C} {f g : Hom A B}
  {Q : Ob C} {coequalize : Hom B Q}
  {cofactorize : forall {Q' : Ob C} {q' : Hom B Q'}, f .> q' == g .> q' -> Hom Q Q'}
  {isCoeq : isCoequalizer C f g Q coequalize (@cofactorize)}.

Arguments cofactorize {Q' q'} _.

Lemma cofactorize_equiv' :
  forall {Q' : Ob C} {h1 h2 : Hom Q Q'},
    h1 == h2 <-> coequalize .> h1 == coequalize .> h2.
Proof.
  split.
  - now intros ->.
  - apply cofactorize_equiv.
Qed.

#[global] Lemma Proper_cofactorize :
  forall {Q' : Ob C} {q1 q2 : Hom B Q'} (H1 : f .> q1 == g .> q1) (H2 : f .> q2 == g .> q2),
    q1 == q2 -> cofactorize H1 == cofactorize H2.
Proof.
  now intros; rewrite cofactorize_equiv', !coequalize_cofactorize.
Qed.

Lemma universal :
  forall
    [Q' : Ob C] [q' : Hom B Q'] (H :  f .> q' == g .> q')
    (h : Hom Q Q'),
      cofactorize H == h <-> coequalize .> h == q'.
Proof.
  split.
  - now intros <-; rewrite coequalize_cofactorize.
  - now intros Heq; rewrite cofactorize_equiv', coequalize_cofactorize.
Qed.

Lemma cofactorize_unique :
  forall
    [Q' : Ob C] [q' : Hom B Q'] (H : f .> q' == g .> q')
    (h : Hom Q Q'),
      coequalize .> h == q' -> h == cofactorize H.
Proof.
  now intros; rewrite cofactorize_equiv', coequalize_cofactorize.
Qed.

Lemma cofactorize_coequalize_ok :
  cofactorize coequalize_ok == id Q.
Proof.
  now rewrite cofactorize_equiv', coequalize_cofactorize, comp_id_r.
Defined.

Lemma isEpi_coequalize :
  isEpi coequalize.
Proof.
  now intros X h1 h2 Heq; rewrite cofactorize_equiv'.
Qed.

Lemma cofactorize_post :
  forall {X Y : Ob C} {q1 : Hom B X} {q2 : Hom X Y}  (H : f .> q1 == g .> q1),
    exists H' : f .> (q1 .> q2) == g .> (q1 .> q2),
      cofactorize H' == cofactorize H .> q2.
Proof.
  esplit. Unshelve. all: cycle 1.
  - now rewrite <- !comp_assoc, H.
  - now rewrite cofactorize_equiv', coequalize_cofactorize, <- comp_assoc, coequalize_cofactorize.
Qed.

End isCoequalizer.

Lemma isCoequalizer_uiso :
  forall
    [C : Cat] [A B : Ob C] [f g : Hom A B]
    (Q1 : Ob C) (q1 : Hom B Q1)
    (cofactorize1 : forall (Q1' : Ob C) (q1' : Hom B Q1'), f .> q1' == g .> q1' -> Hom Q1 Q1')
    (Q2 : Ob C) (q2 : Hom B Q2)
    (cofactorize2 : forall (Q2' : Ob C) (q2' : Hom B Q2'), f .> q2' == g .> q2' -> Hom Q2 Q2'),
      isCoequalizer C f g Q1 q1 cofactorize1 ->
      isCoequalizer C f g Q2 q2 cofactorize2 ->
        exists!! f : Hom Q1 Q2, isIso f /\ q1 .> f == q2.
Proof.
  intros * H1 H2.
  exists (cofactorize1 _ q2 coequalize_ok).
  repeat split.
  - exists (cofactorize2 _ q1 coequalize_ok).
    now rewrite !cofactorize_equiv', <- !comp_assoc, !coequalize_cofactorize, !comp_id_r.
  - now rewrite coequalize_cofactorize.
  - now intros; rewrite cofactorize_equiv', coequalize_cofactorize.
Qed.

Lemma isCoequalizer_iso :
  forall
    [C : Cat] [A B : Ob C] [f g : Hom A B]
    (Q1 : Ob C) (q1 : Hom B Q1)
    (cofactorize1 : forall (Q1' : Ob C) (q1' : Hom B Q1'), f .> q1' == g .> q1' -> Hom Q1 Q1')
    (Q2 : Ob C) (q2 : Hom B Q2)
    (cofactorize2 : forall (Q2' : Ob C) (q2' : Hom B Q2'), f .> q2' == g .> q2' -> Hom Q2 Q2'),
      isCoequalizer C f g Q1 q1 cofactorize1 ->
      isCoequalizer C f g Q2 q2 cofactorize2 ->
        Q1 ~ Q2.
Proof.
  intros. destruct (isCoequalizer_uiso H H0).
  do 2 destruct H1. iso.
Qed.

Lemma isIso_coequalize :
  forall
    [C : Cat] [A B : Ob C] [f g : Hom A B]
    (Q : Ob C) (coequalize : Hom B Q)
    (cofactorize : forall (Q' : Ob C) (q2 : Hom B Q'), f .> q2 == g .> q2 -> Hom Q Q'),
      isCoequalizer C f g Q coequalize cofactorize ->
        isMono coequalize -> isIso coequalize.
Proof.
  unfold isMono, isIso; intros * HC HM.
  assert (Hfg : f .> id B == g .> id B) by (rewrite !comp_id_r; apply HM, coequalize_ok).
  exists (cofactorize B (id B) Hfg).
  now rewrite cofactorize_equiv', <- comp_assoc, !coequalize_cofactorize, comp_id_l, comp_id_r.
Qed.

Context
  [C : Cat]
  [A B : Ob C]
  [f g : Hom A B].

Lemma isCoequalizer_equiv_coequalize :
  forall
    (Q : Ob C) (coequalize1 coequalize2 : Hom B Q)
    (cofactorize : forall (Q' : Ob C) (q2 : Hom B Q'), f .> q2 == g .> q2 -> Hom Q Q'),
      isCoequalizer C f g Q coequalize1 cofactorize ->
      isCoequalizer C f g Q coequalize2 cofactorize ->
        coequalize1 == coequalize2.
Proof.
  now intros; rewrite <- comp_id_r, <- cofactorize_coequalize_ok, coequalize_cofactorize.
Qed.

Lemma isCoequalizer_equiv_cofactorize :
  forall
    (Q : Ob C) (coequalize : Hom B Q)
    (cofactorize1 cofactorize2 : forall (Q' : Ob C) (q2 : Hom B Q'), f .> q2 == g .> q2 -> Hom Q Q'),
      isCoequalizer C f g Q coequalize cofactorize1 ->
      isCoequalizer C f g Q coequalize cofactorize2 ->
        forall (Q' : Ob C) (q' : Hom B Q') (H : f .> q' == g .> q'),
          cofactorize1 Q' q' H == cofactorize2 Q' q' H.
Proof.
  now intros; rewrite cofactorize_equiv', !coequalize_cofactorize.
Qed.

Class HasCoequalizers (C : Cat) : Type :=
{
  coequalizer :
    forall {A B : Ob C} (f g : Hom A B), Ob C;
  coequalize  :
    forall {A B : Ob C} (f g : Hom A B), Hom B (coequalizer f g);
  cofactorize :
    forall {A B : Ob C} (f g : Hom A B) (Q' : Ob C) (q2 : Hom B Q'),
      f .> q2 == g .> q2 -> Hom (coequalizer f g) Q';
  isCoequalizer_HasCoequalizers :>
    forall {A B : Ob C} (f g : Hom A B),
      isCoequalizer C f g (coequalizer f g) (coequalize  f g) (cofactorize f g)
}.

Arguments coequalizer     [C _ A B] _ _.
Arguments coequalize     [C _ A B] _ _.
Arguments cofactorize [C _ A B f g Q' q2] _.