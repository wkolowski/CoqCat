From Cat Require Import Cat.

Set Implicit Arguments.

Class isEqualizer
  (C : Cat) {A B : Ob C} (f g : Hom A B)
  (E : Ob C) (equalize : Hom E A)
  (factorize : forall {E' : Ob C} (e' : Hom E' A), e' .> f == e' .> g -> Hom E' E)
  : Prop :=
{
  ok : equalize .> f == equalize .> g;
  factorize_equalize :
    forall {E' : Ob C} (e' : Hom E' A) (H : e' .> f == e' .> g),
      factorize e' H .> equalize == e';
  equiv_equalizer :
    forall {E' : Ob C} {e1 e2 : Hom E' E},
      e1 .> equalize == e2 .> equalize -> e1 == e2;
}.

#[export] Hint Mode isEqualizer ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isEqualizer ! ! ! - - - - - : core.

Section isEqualizer.

Context
  {C : Cat} {A B : Ob C} {f g : Hom A B}
  {E : Ob C} {equalize : Hom E A}
  {factorize : forall {E' : Ob C} (e' : Hom E' A), e' .> f == e' .> g -> Hom E' E}
  {isEq : isEqualizer C f g E equalize (@factorize)}.

Arguments factorize {E' e'} _.

Lemma equiv_equalizer' :
  forall {E' : Ob C} {e1 e2 : Hom E' E},
    e1 == e2 <-> e1 .> equalize == e2 .> equalize.
Proof.
  split.
  - now intros ->.
  - now apply equiv_equalizer.
Qed.

Lemma Proper_factorize :
  forall {E' : Ob C} {e1 e2 : Hom E' A} (H1 : e1 .> f == e1 .> g) (H2 : e2 .> f == e2 .> g),
    e1 == e2 -> factorize H1 == factorize H2.
Proof.
  now intros; rewrite equiv_equalizer', !factorize_equalize.
Qed.

Lemma universal :
  forall
    [E' : Ob C] [e' : Hom E' A] (H : e' .> f == e' .> g)
    (h : Hom E' E),
      factorize H == h <-> h .> equalize == e'.
Proof.
  split.
  - now intros <-; rewrite factorize_equalize.
  - now intros Heq; rewrite equiv_equalizer', factorize_equalize.
Qed.

Lemma factorize_unique :
  forall
    [E' : Ob C] [e' : Hom E' A] (H : e' .> f == e' .> g)
    (h : Hom E' E),
      h .> equalize == e' -> h == factorize H.
Proof.
  now intros; rewrite equiv_equalizer', factorize_equalize.
Qed.

Lemma factorize_ok :
  factorize ok == id E.
Proof.
  now rewrite equiv_equalizer', factorize_equalize, comp_id_l.
Defined.

(* TODO*) Lemma factorize_comp :
  forall {X Y : Ob C} {e1 : Hom X Y} {e2 : Hom Y A} (H : e2 .> f == e2 .> g),
    exists H' : (e1 .> e2) .> f == (e1 .> e2) .> g,
      factorize H' == e1 .> factorize H.
Proof.
  esplit. Unshelve. all: cycle 1.
  - now rewrite !comp_assoc, H.
  - now rewrite equiv_equalizer', factorize_equalize, comp_assoc, factorize_equalize.
Qed.

Lemma isMono_equalize :
  isMono equalize.
Proof.
  now intros X h1 h2 Heq; rewrite equiv_equalizer'.
Qed.

End isEqualizer.

Ltac equalizer_simpl :=
  repeat (rewrite
    ?equiv_equalizer', ?factorize_equalize, ?factorize_ok,
    ?comp_id_l, ?comp_id_r, ?comp_assoc).

(* TODO: equalize_comp *)

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
  exists (factorize2 E1 equalize1 ok).
  repeat split.
  - exists (factorize1 E2 equalize2 ok).
    now rewrite equiv_equalizer', equiv_equalizer', !comp_assoc, !factorize_equalize, !comp_id_l.
  - now rewrite factorize_equalize.
  - now intros y [_ ?]; rewrite equiv_equalizer', factorize_equalize.
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
  now intros; destruct (isEqualizer_uiso H H0) as [i []]; exists i.
Qed.

Lemma isEqualizer_equiv_equalize :
  forall
    (E : Ob C) (equalize1 equalize2 : Hom E X)
    (factorize : forall (E' : Ob C) (e : Hom E' X), e .> f == e .> g -> Hom E' E),
      isEqualizer C f g E equalize1 factorize ->
      isEqualizer C f g E equalize2 factorize ->
        equalize1 == equalize2.
Proof.
  now intros; rewrite <- comp_id_l, <- factorize_ok, factorize_equalize.
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
  now intros; rewrite equiv_equalizer', !factorize_equalize.
Qed.

Lemma isIso_equalize :
  forall
    (E : Ob C) (equalize : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      isEqualizer C f g E equalize factorize -> isEpi equalize -> isIso equalize.
Proof.
  intros * HisEq HisEpi; red.
  assert (Hfg : id X .> f == id X .> g) by (rewrite !comp_id_l; apply HisEpi, ok).
  exists (factorize _ (id X) Hfg).
  now rewrite equiv_equalizer', comp_assoc, factorize_equalize, comp_id_l, comp_id_r.
Qed.

End Traditional.

Class HasEqualizers (C : Cat) : Type :=
{
  equalizer :
    forall {X Y : Ob C}, Hom X Y -> Hom X Y -> Ob C;
  equalize :
    forall {X Y : Ob C} (f g : Hom X Y), Hom (equalizer f g) X;
  factorize :
    forall [X Y : Ob C] [f g : Hom X Y] [E' : Ob C] (e' : Hom E' X),
      e' .> f == e' .> g -> Hom E' (equalizer f g);
  isEqualizer_HasEqualizers :>
    forall {X Y : Ob C} (f g : Hom X Y),
      isEqualizer C f g (equalizer f g) (equalize f g) (@factorize _ _ f g)
}.

Arguments equalizer     [C _ X Y] _ _.
Arguments equalize    [C _ X Y] _ _.
Arguments factorize [C _ X Y f g E'] _ _.