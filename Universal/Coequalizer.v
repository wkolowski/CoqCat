From Cat Require Import Cat.

Set Implicit Arguments.

Class isCoequalizer
  (C : Cat) {A B : Ob C} (f g : Hom A B)
  (Q : Ob C) (coequalize : Hom B Q)
  (cofactorize : forall {Q' : Ob C} (q : Hom B Q'), f .> q == g .> q -> Hom Q Q')
  : Prop :=
{
  ok : f .> coequalize == g .> coequalize;
  coequalize_cofactorize :
    forall {Q' : Ob C} {q : Hom B Q'} (H : f .> q == g .> q),
      coequalize .> cofactorize q H == q;
  equiv_coequalizer :
    forall {Q' : Ob C} (h1 h2 : Hom Q Q'),
      coequalize .> h1 == coequalize .> h2 -> h1 == h2;
}.

#[export] Hint Mode isCoequalizer ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isCoequalizer ! ! ! - - - - - : core.

Section isCoequalizer.

Context
  {C : Cat} {A B : Ob C} {f g : Hom A B}
  {Q : Ob C} {coequalize : Hom B Q}
  {cofactorize : forall {Q' : Ob C} (q' : Hom B Q'), f .> q' == g .> q' -> Hom Q Q'}
  {isCoeq : isCoequalizer C f g Q coequalize (@cofactorize)}.

Arguments cofactorize {Q' q'} _.

Lemma equiv_coequalizer' :
  forall {Q' : Ob C} {h1 h2 : Hom Q Q'},
    h1 == h2 <-> coequalize .> h1 == coequalize .> h2.
Proof.
  split.
  - now intros ->.
  - now apply equiv_coequalizer.
Qed.

#[global] Lemma Proper_cofactorize :
  forall {Q' : Ob C} {q1 q2 : Hom B Q'} (H1 : f .> q1 == g .> q1) (H2 : f .> q2 == g .> q2),
    q1 == q2 -> cofactorize H1 == cofactorize H2.
Proof.
  now intros; rewrite equiv_coequalizer', !coequalize_cofactorize.
Qed.

Lemma universal :
  forall
    [Q' : Ob C] [q' : Hom B Q'] (H :  f .> q' == g .> q')
    (h : Hom Q Q'),
      cofactorize H == h <-> coequalize .> h == q'.
Proof.
  split.
  - now intros <-; rewrite coequalize_cofactorize.
  - now intros Heq; rewrite equiv_coequalizer', coequalize_cofactorize.
Qed.

Lemma cofactorize_unique :
  forall
    [Q' : Ob C] [q' : Hom B Q'] (H : f .> q' == g .> q')
    (h : Hom Q Q'),
      coequalize .> h == q' -> h == cofactorize H.
Proof.
  now intros; rewrite equiv_coequalizer', coequalize_cofactorize.
Qed.

Lemma cofactorize_ok :
  cofactorize ok == id Q.
Proof.
  now rewrite equiv_coequalizer', coequalize_cofactorize, comp_id_r.
Defined.

Lemma isEpi_coequalize :
  isEpi coequalize.
Proof.
  now intros X h1 h2 Heq; rewrite equiv_coequalizer'.
Qed.

Lemma comp_cofactorize :
  forall {X Y : Ob C} {q1 : Hom B X} {q2 : Hom X Y}  (Heq : f .> q1 == g .> q1),
    cofactorize Heq .> q2 == cofactorize (wut_r q2 Heq).
Proof.
  now intros; rewrite equiv_coequalizer', coequalize_cofactorize, <- comp_assoc,
    coequalize_cofactorize.
Qed.

End isCoequalizer.

Ltac coequalizer_simpl :=
  repeat (rewrite
    ?comp_cofactorize, ?equiv_coequalizer', ?coequalize_cofactorize, ?cofactorize_ok,
    ?comp_id_l, ?comp_id_r, <- ?comp_assoc).

Section Traditional.

Context
  [C : Cat]
  [A B : Ob C]
  [f g : Hom A B].

Lemma isCoequalizer_uiso :
  forall
    (Q1 : Ob C) (q1 : Hom B Q1)
    (cofactorize1 : forall (Q1' : Ob C) (q1' : Hom B Q1'), f .> q1' == g .> q1' -> Hom Q1 Q1')
    (Q2 : Ob C) (q2 : Hom B Q2)
    (cofactorize2 : forall (Q2' : Ob C) (q2' : Hom B Q2'), f .> q2' == g .> q2' -> Hom Q2 Q2'),
      isCoequalizer C f g Q1 q1 cofactorize1 ->
      isCoequalizer C f g Q2 q2 cofactorize2 ->
        exists!! f : Hom Q1 Q2, isIso f /\ q1 .> f == q2.
Proof.
  intros * H1 H2.
  exists (cofactorize1 _ q2 ok).
  repeat split.
  - exists (cofactorize2 _ q1 ok).
    now rewrite !equiv_coequalizer', <- !comp_assoc, !coequalize_cofactorize, !comp_id_r.
  - now rewrite coequalize_cofactorize.
  - now intros; rewrite equiv_coequalizer', coequalize_cofactorize.
Qed.

Lemma isCoequalizer_iso :
  forall
    (Q1 : Ob C) (q1 : Hom B Q1)
    (cofactorize1 : forall (Q1' : Ob C) (q1' : Hom B Q1'), f .> q1' == g .> q1' -> Hom Q1 Q1')
    (Q2 : Ob C) (q2 : Hom B Q2)
    (cofactorize2 : forall (Q2' : Ob C) (q2' : Hom B Q2'), f .> q2' == g .> q2' -> Hom Q2 Q2'),
      isCoequalizer C f g Q1 q1 cofactorize1 ->
      isCoequalizer C f g Q2 q2 cofactorize2 ->
        Q1 ~ Q2.
Proof.
  now intros * H1 H2; destruct (isCoequalizer_uiso H1 H2) as [i []]; exists i.
Qed.

Lemma isIso_coequalize :
  forall
    (Q : Ob C) (coequalize : Hom B Q)
    (cofactorize : forall (Q' : Ob C) (q2 : Hom B Q'), f .> q2 == g .> q2 -> Hom Q Q'),
      isCoequalizer C f g Q coequalize cofactorize ->
        isMono coequalize -> isIso coequalize.
Proof.
  unfold isMono, isIso; intros * HC HM.
  assert (Hfg : f .> id B == g .> id B) by (rewrite !comp_id_r; apply HM, ok).
  exists (cofactorize B (id B) Hfg).
  now rewrite equiv_coequalizer', <- comp_assoc, !coequalize_cofactorize, comp_id_l, comp_id_r.
Qed.

Lemma isCoequalizer_equiv_coequalize :
  forall
    (Q : Ob C) (coequalize1 coequalize2 : Hom B Q)
    (cofactorize : forall (Q' : Ob C) (q2 : Hom B Q'), f .> q2 == g .> q2 -> Hom Q Q'),
      isCoequalizer C f g Q coequalize1 cofactorize ->
      isCoequalizer C f g Q coequalize2 cofactorize ->
        coequalize1 == coequalize2.
Proof.
  now intros; rewrite <- comp_id_r, <- cofactorize_ok, coequalize_cofactorize.
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
  now intros; rewrite equiv_coequalizer', !coequalize_cofactorize.
Qed.

End Traditional.

Class HasCoequalizers (C : Cat) : Type :=
{
  coequalizer :
    forall {A B : Ob C} (f g : Hom A B), Ob C;
  coequalize  :
    forall {A B : Ob C} (f g : Hom A B), Hom B (coequalizer f g);
  cofactorize :
    forall [A B : Ob C] [f g : Hom A B] [Q' : Ob C] (q2 : Hom B Q'),
      f .> q2 == g .> q2 -> Hom (coequalizer f g) Q';
  isCoequalizer_HasCoequalizers ::
    forall {A B : Ob C} (f g : Hom A B),
      isCoequalizer C f g (coequalizer f g) (coequalize  f g) (@cofactorize _ _ f g)
}.

Arguments coequalizer [C _ A B] _ _.
Arguments coequalize  [C _ A B] _ _.
Arguments cofactorize [C _ A B f g Q'] _ _.