From Cat Require Import Cat.

Set Implicit Arguments.

Class isEqualizer
  (C : Cat) {A B : Ob C} (f g : Hom A B)
  (E : Ob C) (equalize : Hom E A)
  (factorize : forall {E' : Ob C} {e' : Hom E' A}, e' .> f == e' .> g -> Hom E' E)
  : Prop :=
{
  equalize_ok : equalize .> f == equalize .> g;
  factorize_equalize :
    forall {E' : Ob C} {e' : Hom E' A} (H : e' .> f == e' .> g),
      factorize H .> equalize == e';
  factorize_equiv :
    forall {E' : Ob C} {e1 e2 : Hom E' E},
      e1 .> equalize == e2 .> equalize -> e1 == e2;
}.

#[export] Hint Mode isEqualizer ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isEqualizer ! ! ! - - - - - : core.

Section isEqualizer.

Context
  {C : Cat} {A B : Ob C} {f g : Hom A B}
  {E : Ob C} {equalize : Hom E A}
  {factorize : forall {E' : Ob C} {e' : Hom E' A}, e' .> f == e' .> g -> Hom E' E}
  {isEq : isEqualizer C f g E equalize (@factorize)}.

Arguments factorize {E' e'} _.

Lemma factorize_equiv' :
  forall {E' : Ob C} {e1 e2 : Hom E' E},
    e1 == e2 <-> e1 .> equalize == e2 .> equalize.
Proof.
  split.
  - now intros ->.
  - apply factorize_equiv.
Qed.

#[global] Lemma Proper_factorize :
  forall {E' : Ob C} {e1 e2 : Hom E' A} (H1 : e1 .> f == e1 .> g) (H2 : e2 .> f == e2 .> g),
    e1 == e2 -> factorize H1 == factorize H2.
Proof.
  now intros; rewrite factorize_equiv', !factorize_equalize.
Qed.

Lemma universal :
  forall
    [E' : Ob C] [e' : Hom E' A] (H : e' .> f == e' .> g)
    (h : Hom E' E),
      factorize H == h <-> h .> equalize == e'.
Proof.
  split.
  - now intros <-; rewrite factorize_equalize.
  - now intros Heq; rewrite factorize_equiv', factorize_equalize.
Qed.

Lemma factorize_unique :
  forall
    [E' : Ob C] [e' : Hom E' A] (H : e' .> f == e' .> g)
    (h : Hom E' E),
      h .> equalize == e' -> h == factorize H.
Proof.
  now intros; rewrite factorize_equiv', factorize_equalize.
Qed.

Lemma factorize_equalize_ok :
  factorize equalize_ok == id E.
Proof.
  now rewrite factorize_equiv', factorize_equalize, comp_id_l.
Defined.

Lemma factorize_pre :
  forall {X Y : Ob C} {e1 : Hom X Y} {e2 : Hom Y A} (H : e2 .> f == e2 .> g),
    exists H' : (e1 .> e2) .> f == (e1 .> e2) .> g,
      factorize H' == e1 .> factorize H.
Proof.
  esplit. Unshelve. all: cycle 1.
  - now rewrite !comp_assoc, H.
  - now rewrite factorize_equiv', factorize_equalize, comp_assoc, factorize_equalize.
Qed.

Lemma isMono_equalize :
  isMono equalize.
Proof.
  now intros X h1 h2 Heq; rewrite factorize_equiv'.
Qed.

End isEqualizer.

Section Traditional.

Context
  [C : Cat]
  [X Y : Ob C]
  [f g : Hom X Y].

Lemma isEqualizer_uiso :
  forall
    {E1 : Ob C} {equalize1 : Hom E1 X}
    {factorize1 : forall (E1' : Ob C) (e1' : Hom E1' X), e1' .> f == e1' .> g -> Hom E1' E1}
    {E2 : Ob C} {equalize2 : Hom E2 X}
    {factorize2 : forall (E2' : Ob C) (e2' : Hom E2' X), e2' .> f == e2' .> g -> Hom E2' E2},
      isEqualizer C f g E1 equalize1 factorize1 ->
      isEqualizer C f g E2 equalize2 factorize2 ->
        exists!! f : Hom E1 E2, isIso f /\ equalize1 == f .> equalize2.
Proof.
  intros * H1 H2.
  exists (factorize2 E1 equalize1 equalize_ok).
  repeat split.
  - exists (factorize1 E2 equalize2 equalize_ok).
    now rewrite factorize_equiv', factorize_equiv', !comp_assoc, !factorize_equalize, !comp_id_l.
  - now rewrite factorize_equalize.
  - now intros y [_ ?]; rewrite factorize_equiv', factorize_equalize.
Qed.

Lemma isEqualizer_iso :
  forall
    {E1 : Ob C} {e1 : Hom E1 X}
    {factorize1 : forall (E1' : Ob C) (e1' : Hom E1' X), e1' .> f == e1' .> g -> Hom E1' E1}
    {E2 : Ob C} {e2 : Hom E2 X}
    {factorize2 : forall (E2' : Ob C) (e2' : Hom E2' X), e2' .> f == e2' .> g -> Hom E2' E2},
      isEqualizer C f g E1 e1 factorize1 ->
      isEqualizer C f g E2 e2 factorize2 ->
        E1 ~ E2.
Proof.
  intros. destruct (isEqualizer_uiso H H0).
  do 2 destruct H1. eauto.
Qed.

Lemma isEqualizer_equiv_equalize :
  forall
    (E : Ob C) (equalize1 equalize2 : Hom E X)
    (factorize : forall (E' : Ob C) (e : Hom E' X), e .> f == e .> g -> Hom E' E),
      isEqualizer C f g E equalize1 factorize ->
      isEqualizer C f g E equalize2 factorize ->
        equalize1 == equalize2.
Proof.
  now intros; rewrite <- comp_id_l, <- factorize_equalize_ok, factorize_equalize.
Qed.

Lemma isEqualizer_equiv_factorize :
  forall
    (E : Ob C) (equalize : Hom E X)
    (factorize1 factorize2 : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      isEqualizer C f g E equalize factorize1 ->
      isEqualizer C f g E equalize factorize2 ->
        forall (E' : Ob C) (e' : Hom E' X) (H : e' .> f == e' .> g),
          factorize1 E' e' H == factorize2 E' e' H.
Proof.
  now intros; rewrite factorize_equiv', !factorize_equalize.
Qed.

Lemma isIso_equalize :
  forall
    (E : Ob C) (equalize : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      isEqualizer C f g E equalize factorize -> isEpi equalize -> isIso equalize.
Proof.
  intros * HisEq HisEpi; red.
  assert (Hfg : id X .> f == id X .> g) by (rewrite !comp_id_l; apply HisEpi, equalize_ok).
  exists (factorize _ (id X) Hfg).
  now rewrite factorize_equiv', comp_assoc, factorize_equalize, comp_id_l, comp_id_r.
Qed.

End Traditional.

Class HasEqualizers (C : Cat) : Type :=
{
  eq_ob :
    forall {X Y : Ob C}, Hom X Y -> Hom X Y -> Ob C;
  equalize :
    forall {X Y : Ob C} (f g : Hom X Y), Hom (eq_ob f g) X;
  factorize :
    forall [X Y : Ob C] [f g : Hom X Y] [E' : Ob C] [e' : Hom E' X],
      e' .> f == e' .> g -> Hom E' (eq_ob f g);
  HasEqualizers_isEqualizer :>
    forall {X Y : Ob C} (f g : Hom X Y),
      isEqualizer C f g (eq_ob f g) (equalize f g) (@factorize _ _ f g)
  (*Proper_eq_ob :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (id (eq_ob f g)) (id (eq_ob f' g'));
  Proper_equalize :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' ->
        JMequiv (equalize f g) (equalize f' g'); *)
}.

Arguments eq_ob     [C _ X Y] _ _.
Arguments equalize    [C _ X Y] _ _.
Arguments factorize [C _ X Y f g E' e'] _.
