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
  {C : Cat} {A B : Ob C} (f g : Hom A B)
  {E : Ob C} {equalize : Hom E A}
  {factorize : forall {E' : Ob C} {e' : Hom E' A}, e' .> f == e' .> g -> Hom E' E}
  {isEq : isEqualizer C f g E equalize (@factorize)}.

Arguments factorize {E' e'} _.

Lemma factorize_equiv' :
  forall {E' : Ob C} {e1 e2 : Hom E' E},
    e1 == e2 <-> e1 .> equalize == e2 .> equalize.
Proof.
  split.
  - intros ->; reflexivity.
  - apply factorize_equiv.
Qed.

Lemma universal :
  forall
    [E' : Ob C] [e' : Hom E' A] (H : e' .> f == e' .> g)
    (h : Hom E' E),
      factorize H == h <-> h .> equalize == e'.
Proof.
  split.
  - intros <-. apply factorize_equalize.
  - intros Heq. apply factorize_equiv.
    rewrite factorize_equalize. symmetry. assumption.
Qed.

Lemma factorize_unique :
  forall
    [E' : Ob C] [e' : Hom E' A] (H : e' .> f == e' .> g)
    (h : Hom E' E),
      h .> equalize == e' -> h == factorize H.
Proof.
  intros * Heq.
  apply factorize_equiv.
  rewrite factorize_equalize.
  assumption.
Restart.
  intros * Heq.
  rewrite factorize_equiv', factorize_equalize, Heq.
  reflexivity.
Qed.

Lemma factorize_equalize_ok :
  factorize equalize_ok == id E.
Proof.
  apply factorize_equiv.
  rewrite factorize_equalize, comp_id_l.
  reflexivity.
Restart.
  rewrite factorize_equiv', factorize_equalize, comp_id_l.
  reflexivity.
Defined.

Lemma isMono_equalize :
  isMono equalize.
Proof.
  intros X h1 h2 Heq.
  rewrite factorize_equiv'.
  assumption.
Qed.

Lemma factorize_pre :
  forall {X Y : Ob C} {e1 : Hom X Y} {e2 : Hom Y A} (H : (e1 .> e2) .> f == (e1 .> e2) .> g),
    exists H' : e2 .> f == e2 .> g,
      factorize H == e1 .> factorize H'.
Proof.
  intros.
  assert (H' : e2 .> f == e2 .> g).
  {
    admit.
  }
  exists H'.
  rewrite factorize_equiv', comp_assoc, !factorize_equalize.
  reflexivity.
Admitted.

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
    split.
    + apply factorize_equiv.
      rewrite comp_assoc, !factorize_equalize, comp_id_l.
      reflexivity.
    + apply factorize_equiv.
      rewrite comp_assoc, !factorize_equalize, comp_id_l.
      reflexivity.
  - rewrite factorize_equalize.
    reflexivity.
  - intros y [_ Heq].
    apply factorize_equiv.
    rewrite factorize_equalize.
    assumption.
Restart.
  intros * H1 H2.
  exists (factorize2 E1 equalize1 equalize_ok).
  repeat split.
  - exists (factorize1 E2 equalize2 equalize_ok).
    rewrite (factorize_equiv' (isEq := H1)), (factorize_equiv' (isEq := H2)),
      !comp_assoc, !factorize_equalize, !comp_id_l.
    split; reflexivity.
  - rewrite factorize_equalize.
    reflexivity.
  - intros y [_ Heq].
    rewrite (factorize_equiv' (isEq := H2)), factorize_equalize.
    assumption.
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
  intros * H1 H2.
  rewrite <- comp_id_l, <- (factorize_equalize_ok (isEq := H2)), factorize_equalize.
  reflexivity.
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
  intros.
  apply factorize_equiv.
  rewrite !factorize_equalize.
  reflexivity.
Restart.
  intros.
  rewrite (factorize_equiv' (isEq := H)), !factorize_equalize.
  reflexivity.
Qed.

Lemma isEqualizer_epi_is_iso :
  forall
    (E : Ob C) (equalize : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      isEqualizer C f g E equalize factorize -> isEpi equalize -> isIso equalize.
Proof.
  intros * HisEq HisEpi; red.
  assert (Hfg : id X .> f == id X .> g).
  {
    apply HisEpi.
    rewrite !comp_id_l.
    apply equalize_ok.
  }
  exists (factorize _ (id X) Hfg).
  split.
  - apply factorize_equiv.
    rewrite comp_assoc, factorize_equalize, comp_id_l, comp_id_r.
    reflexivity.
  - rewrite factorize_equalize. reflexivity.
Restart.
  intros * HisEq HisEpi; red.
  assert (Hfg : id X .> f == id X .> g).
  {
    apply HisEpi.
    rewrite !comp_id_l.
    apply equalize_ok.
  }
  exists (factorize _ (id X) Hfg).
  split.
  - rewrite (factorize_equiv' (isEq := HisEq)), comp_assoc,
      factorize_equalize, comp_id_l, comp_id_r.
    reflexivity.
  - rewrite factorize_equalize. reflexivity.
Qed.

End Traditional.