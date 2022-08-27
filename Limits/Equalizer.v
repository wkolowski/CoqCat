From Cat Require Import Cat.

Set Implicit Arguments.

Definition isEqualizer
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (E : Ob C) (e : Hom E X)
  (factorize : forall {E' : Ob C} {e' : Hom E' X}, e' .> f == e' .> g -> Hom E' E)
  : Prop :=
    e .> f == e .> g
      /\
    forall (E' : Ob C) (e' : Hom E' X) (H : e' .> f == e' .> g),
      setoid_unique (fun u : Hom E' E => u .> e == e') (factorize H).

Section Traditional.

Context
  [C : Cat]
  [X Y : Ob C]
  [f g : Hom X Y].

Lemma isEqualizer_uiso :
  forall
    {E1 : Ob C} {e1 : Hom E1 X}
    {factorize1 : forall (E1' : Ob C) (e1' : Hom E1' X), e1' .> f == e1' .> g -> Hom E1' E1}
    {E2 : Ob C} {e2 : Hom E2 X}
    {factorize2 : forall (E2' : Ob C) (e2' : Hom E2' X), e2' .> f == e2' .> g -> Hom E2' E2},
      isEqualizer C f g E1 e1 factorize1 ->
      isEqualizer C f g E2 e2 factorize2 ->
        exists!! f : Hom E1 E2, isIso f /\ e1 == f .> e2.
Proof.
  unfold isEqualizer; intros. destruct H, H0.
  destruct
    (H1 E1 e1 H) as [eq1 unique1],
    (H1 E2 e2 H0) as [eq1' unique1'],
    (H2 E2 e2 H0) as [eq2 unique2],
    (H2 E1 e1 H) as [eq2' unique2'].
  exists (factorize2 E1 e1 H).
  repeat split.
    red. exists (factorize1 E2 e2 H0). split.
      assert (Heq : (factorize2 E1 e1 H .> e2) .> f == (factorize2 E1 e1 H .> e2) .> g).
        now rewrite eq2'.
        destruct (H1 E1 (factorize2 E1 e1 H .> e2) Heq).
          rewrite <- (unique1 (factorize2 E1 e1 H .> factorize1 E2 e2 H0)).
            auto.
            assocr. rewrite eq1'. auto.
          rewrite <- (unique2 (factorize1 E2 e2 H0 .> factorize2 E1 e1 H)).
            auto.
            assocr. rewrite eq2'. auto.
    rewrite eq2'. reflexivity.
    intros. destruct H3. apply unique2'. rewrite H4. reflexivity.
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

Lemma isEqualizer_equiv :
  forall
    (E : Ob C) (e1 e2 : Hom E X)
    (factorize : forall (E' : Ob C) (e : Hom E' X), e .> f == e .> g -> Hom E' E),
      isEqualizer C f g E e1 factorize ->
      isEqualizer C f g E e2 factorize ->
        e1 == e2.
Proof.
  intros. edestruct H, H0, (H4 _ _ H3).
  assert (factorize E e2 H3 == id E).
    apply H6. cat.
    edestruct (H2 _ _ H3). rewrite H7 in H8. cat.
Qed.

Lemma isEqualizer_equiv_factorize :
  forall
    (E : Ob C) (e : Hom E X)
    (factorize1 factorize2 : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      isEqualizer C f g E e factorize1 ->
      isEqualizer C f g E e factorize2 ->
        forall (E' : Ob C) (e' : Hom E' X) (H : e' .> f == e' .> g),
          factorize1 E' e' H == factorize2 E' e' H.
Proof.
  intros.
  edestruct H, H3. apply H5.
  edestruct H0, H7. apply H8.
Qed.

Lemma isMono_equalizer :
  forall
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      isEqualizer C f g E e factorize -> isMono e.
Proof.
  unfold isEqualizer, setoid_unique, isMono. intros.
  rename X0 into Z. rename g0 into h'.
  destruct H as [eq H].
  assert ((h .> e) .> f == (h .> e) .> g).
    assocr'. rewrite eq. reflexivity.
  assert ((h' .> e) .> f == (h' .> e) .> g).
    assocr'. rewrite eq. reflexivity.
  destruct (H Z (h .> e) H1) as [u Hh].
  edestruct (H Z (h' .> e) H2) as [u' Hh'].
  assert (factorize Z (h .> e) H1 == factorize Z (h' .> e) H2).
    rewrite Hh, Hh'. reflexivity. reflexivity. assumption.
  specialize (Hh h); specialize (Hh' h').
  rewrite <- Hh, <- Hh'; try rewrite H3; reflexivity.
Defined.

Lemma isEqualizer_epi_is_iso :
  forall
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      isEqualizer C f g E e factorize -> isEpi e -> isIso e.
Proof.
  intros. assert (HisMono : isMono e).
    eapply isMono_equalizer; eauto.
    unfold isEpi, isMono in *. destruct H.
    red. pose (Heq := H0 _ _ _ H). assert (id X .> f == id X .> g).
      cat.
      exists (factorize _ (id X) H2). split.
        edestruct H1. assert (e .> factorize X (id X) H2 .> e == id E .> e).
          assocr. rewrite H3. cat.
          rewrite (HisMono _ _ _ H5). reflexivity.
        edestruct H1. apply H3.
Qed.

End Traditional.

Class HasEqualizers (C : Cat) : Type :=
{
  equalizer :
    forall {X Y : Ob C}, Hom X Y -> Hom X Y -> Ob C;
  Proper_equalizer :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (id (equalizer f g)) (id (equalizer f' g'));
  eq_mor :
    forall {X Y : Ob C} (f g : Hom X Y), Hom (equalizer f g) X;
  eq_mor_ok :
    forall (X Y : Ob C) (f g : Hom X Y),
      eq_mor f g .> f == eq_mor f g .> g;
  Proper_eq_mor :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' ->
        JMequiv (eq_mor f g) (eq_mor f' g');
  factorize :
    forall [X Y : Ob C] [f g : Hom X Y] [E' : Ob C] [e' : Hom E' X],
      e' .> f == e' .> g -> Hom E' (equalizer f g);
  (* Proper_factorize :
    forall
      (X Y E' : Ob C) (f f' g g' : Hom X Y) (e' : Hom E' X)
      (H : e' .> f == e' .> g) (H' : e' .> f' == e' .> g'),
        f == f' -> g == g' -> JMequiv (factorize H) (factorize H'); *)
  is_equalizer :
    forall (X Y : Ob C) (f g : Hom X Y),
      isEqualizer C f g (equalizer f g) (eq_mor f g) (@factorize _ _ f g)
}.

Arguments equalizer     [C _ X Y] _ _.
Arguments eq_mor    [C _ X Y] _ _.
Arguments factorize [C _ X Y f g E' e'] _.

Section HasEqualizers.

Context
  [C : Cat] [heq : HasEqualizers C]
  [X Y : Ob C]
  [f g : Hom X Y].

Lemma universal :
  forall
    [E' : Ob C] [e' : Hom E' X] (H : e' .> f == e' .> g)
    (h : Hom E' (equalizer f g)),
      factorize H == h <-> h .> eq_mor f g == e'.
Proof.
  intros.
  destruct (is_equalizer X Y f g) as [H1 H2]; unfold setoid_unique in H2.
  split.
  - intros <-. apply H2.
  - intros Heq.
    destruct (H2 _ _ H) as [_ H2'].
    apply H2'.
    assumption.
Qed.

Lemma factorize_eq_mor :
  forall {E' : Ob C} {e' : Hom E' X} (H : e' .> f == e' .> g),
    factorize H .> eq_mor f g == e'.
Proof.
  intros.
  destruct (is_equalizer X Y f g) as [_ H'].
  apply H'.
Qed.

Lemma isMono_eq_mor :
  isMono (eq_mor f g).
Proof.
  intros A h1 h2 Heq.
  assert (H1 : (h1 .> eq_mor f g) .> f == (h1 .> eq_mor f g) .> g)
    by (rewrite !comp_assoc, eq_mor_ok; reflexivity).
  destruct (@universal _ (h1 .> eq_mor f g) H1 h1) as [_ <-]; [| reflexivity].
  destruct (@universal _ (h1 .> eq_mor f g) H1 h2) as [_ <-].
  - reflexivity.
  - symmetry. assumption.
Qed.

End HasEqualizers.

Lemma factorize_eq_mor' :
  forall [C : Cat] (he : HasEqualizers C) [X Y : Ob C] (f g : Hom X Y),
    factorize (proj1 (is_equalizer X Y f g)) == id (equalizer f g).
Proof.
  intros. destruct he; cbn in *.
  edestruct is_equalizer0, s. cat.
Defined.

Lemma factorize_eq_mor'' :
  forall [C : Cat] (he : HasEqualizers C) [X Y : Ob C] (f g : Hom X Y),
    factorize (eq_mor_ok X Y f g) == id (equalizer f g).
Proof.
  intros.
  apply universal.
  rewrite comp_id_l.
  reflexivity.
Defined.

(*
TODO Lemma factorize_comp :
  forall
    (C : Cat) (he : HasEqualizers C)
    (X Y A : Ob C) (f g : Hom X Y)
    (h1 : Hom (equalizer f g) A) (h2 : Hom A X)
    (H : h1 .> h2 .> f == h1 .> h2 .> g),
      factorize f g _ (h1 .> h2) H ==
(*      id (equalizer f g).*)
Proof.
  intros. destruct he; cbn in *.
  destruct (is_equalizer0 _ _ f g).
  edestruct is_equalizer0, H1. rewrite H3. reflexivity. reflexivity. cat. apply H3. s. cat.
Defined.
*)

Module Universal.

Class HasEqualizers (C : Cat) : Type :=
{
  equalizer :
    forall {X Y : Ob C}, Hom X Y -> Hom X Y -> Ob C;
  Proper_equalizer :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (id (equalizer f g)) (id (equalizer f' g'));
  eq_mor :
    forall {X Y : Ob C} (f g : Hom X Y), Hom (equalizer f g) X;
  eq_mor_ok :
    forall (X Y : Ob C) (f g : Hom X Y),
      eq_mor f g .> f == eq_mor f g .> g;
  Proper_eq_mor :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' ->
        JMequiv (eq_mor f g) (eq_mor f' g');
  factorize :
    forall [X Y : Ob C] [f g : Hom X Y] [E' : Ob C] [e' : Hom E' X],
      e' .> f == e' .> g -> Hom E' (equalizer f g);
  (* Proper_factorize :
    forall
      (X Y E' : Ob C) (f f' g g' : Hom X Y) (e' : Hom E' X)
      (H : e' .> f == e' .> g) (H' : e' .> f' == e' .> g'),
        f == f' -> g == g' -> JMequiv (factorize H) (factorize H'); *)
  universal :
    forall
      {X Y : Ob C} [f g : Hom X Y]
      [E' : Ob C] [e' : Hom E' X] (H : e' .> f == e' .> g)
      (h : Hom E' (equalizer f g)),
        factorize H == h <-> h .> eq_mor f g == e'
}.

Arguments equalizer     [C _ X Y] _ _.
Arguments eq_mor    [C _ X Y] _ _.
Arguments factorize [C _ X Y f g E' e'] _.

Section HasEqualizers.

Context
  [C : Cat] [heq : HasEqualizers C]
  [X Y : Ob C]
  [f g : Hom X Y].

Lemma factorize_eq_mor :
  forall {E' : Ob C} {e' : Hom E' X} (H : e' .> f == e' .> g),
    factorize H .> eq_mor f g == e'.
Proof.
  intros.
  rewrite <- universal.
  reflexivity.
Qed.

Lemma isMono_eq_mor :
  isMono (eq_mor f g).
Proof.
  intros A h1 h2 Heq.
  assert (H1 : (h1 .> eq_mor f g) .> f == (h1 .> eq_mor f g) .> g)
    by (rewrite !comp_assoc, eq_mor_ok; reflexivity).
  destruct (@universal _ _ _ _ f g _ (h1 .> eq_mor f g) H1 h1) as [_ <-]; [| reflexivity].
  destruct (@universal _ _ _ _ f g _ (h1 .> eq_mor f g) H1 h2) as [_ <-].
  - reflexivity.
  - symmetry. assumption.
Qed.

End HasEqualizers.

End Universal.

Module UniversalEquiv.

#[export]
Instance to (C : Cat) (heq : HasEqualizers C) : Universal.HasEqualizers C :=
{
  equalizer := @equalizer C heq;
  Proper_equalizer := @Proper_equalizer C heq;
  eq_mor := @eq_mor C heq;
  Proper_eq_mor := @Proper_eq_mor C heq;
  eq_mor_ok := @eq_mor_ok C heq;
  factorize := @factorize C heq;
  universal := @universal C heq;
}.

#[refine]
#[export]
Instance from (C : Cat) (heq : Universal.HasEqualizers C) : HasEqualizers C :=
{
  equalizer := @Universal.equalizer C heq;
  Proper_equalizer := @Universal.Proper_equalizer C heq;
  eq_mor := @Universal.eq_mor C heq;
  Proper_eq_mor := @Universal.Proper_eq_mor C heq;
  eq_mor_ok := @Universal.eq_mor_ok C heq;
  factorize := @Universal.factorize C heq;
}.
Proof.
  unfold isEqualizer, setoid_unique.
  intros X Y f g; split.
  - apply Universal.eq_mor_ok.
  - intros. split.
    + apply Universal.factorize_eq_mor.
    + intros h Heq. apply Universal.universal. assumption.
Defined.

End UniversalEquiv.