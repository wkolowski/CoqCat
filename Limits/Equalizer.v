From Cat Require Import Cat.

Set Implicit Arguments.

Definition equalizer
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (E : Ob C) (e : Hom E X)
  (factorize : forall {E' : Ob C} {e' : Hom E' X}, e' .> f == e' .> g -> Hom E' E)
  : Prop :=
    e .> f == e .> g
      /\
    forall (E' : Ob C) (e' : Hom E' X) (H : e' .> f == e' .> g),
      setoid_unique (fun u : Hom E' E => u .> e == e') (factorize H).

#[refine]
#[export]
Instance SetoidFunExt_setoid (A B : Type) (A' : Setoid A) (B' : Setoid B) : Setoid (A -> B) :=
{
  equiv := fun f g : A -> B => forall x : A, f x == g x
}.
Proof. solve_equiv. Defined.

Class HasEqualizers (C : Cat) : Type :=
{
  eq_ob :
    forall {X Y : Ob C}, Hom X Y -> Hom X Y -> Ob C;
  Proper_eq_ob :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (id (eq_ob f g)) (id (eq_ob f' g'));
  eq_mor :
    forall {X Y : Ob C} (f g : Hom X Y), Hom (eq_ob f g) X;
  Proper_eq_mor :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> (*eq_ob f g = eq_ob f' g' ->*)
        JMequiv (eq_mor f g) (eq_mor f' g');
  factorize :
    forall {X Y : Ob C} (f g : Hom X Y) (E' : Ob C) (e' : Hom E' X),
      e' .> f == e' .> g -> Hom E' (eq_ob f g);
  (* TODO: Proper_factorize :
    forall
      (X Y E' : Ob C) (f f' g g' : Hom X Y) (e' : Hom E' X)
      (H : e' .> f == e' .> g) (H' : e' .> f' == e' .> g'),
        f == f' -> g == g' -> JMequiv (factorize f g E' e' H) (factorize f' g' E' e' H'); *)
  is_equalizer :
    forall (X Y : Ob C) (f g : Hom X Y),
      equalizer C f g (eq_ob f g) (eq_mor f g) (factorize f g)
}.

Arguments eq_ob     [C _ X Y] _ _.
Arguments eq_mor    [C _ X Y] _ _.
Arguments factorize [C _ X Y f g E' e'] _.

Section HasEqualizers.

Context
  [C : Cat]
  [X Y : Ob C]
  [f g : Hom X Y].

Lemma equalizer_uiso :
  forall
    {E : Ob C} {e : Hom E X}
    {factorize : forall (E'' : Ob C) (e'' : Hom E'' X), e'' .> f == e'' .> g -> Hom E'' E}
    {E' : Ob C} {e' : Hom E' X}
    {factorize' : forall (E'' : Ob C) (e'' : Hom E'' X), e'' .> f == e'' .> g -> Hom E'' E'},
      equalizer C f g E e factorize -> equalizer C f g E' e' factorize' ->
        exists!! f : Hom E E', Iso f /\ e == f .> e'.
Proof.
  unfold equalizer; intros. destruct H, H0.
  destruct
    (H1 E e H) as [eq1 unique1],
    (H1 E' e' H0) as [eq1' unique1'],
    (H2 E' e' H0) as [eq2 unique2],
    (H2 E e H) as [eq2' unique2'].
  exists (factorize' E e H).
  repeat split.
    red. exists (factorize0 E' e' H0). split.
      assert (Heq : (factorize' E e H .> e') .> f ==
        (factorize' E e H .> e') .> g).
        rewrite eq2'. trivial.
        destruct (H1 E (factorize' E e H .> e') Heq).
          rewrite <- (unique1 (factorize' E e H .> factorize0 E' e' H0)).
            auto.
            assocr. rewrite eq1'. auto.
          rewrite <- (unique2 (factorize0 E' e' H0 .> factorize' E e H)).
            auto.
            assocr. rewrite eq2'. auto.
    rewrite eq2'. reflexivity.
    intros. destruct H3. apply unique2'. rewrite H4. reflexivity.
Qed.

Lemma equalizer_iso :
  forall
    (E E' : Ob C) (e : Hom E X) (e' : Hom E' X)
    (factorize : forall (E'' : Ob C) (e'' : Hom E'' X), e'' .> f == e'' .> g -> Hom E'' E)
    (factorize' : forall (E'' : Ob C) (e'' : Hom E'' X), e'' .> f == e'' .>g -> Hom E'' E'),
      equalizer C f g E e factorize -> equalizer C f g E' e' factorize' -> E ~ E'.
Proof.
  intros. destruct (equalizer_uiso H H0).
  do 2 destruct H1. eauto.
Qed.

Lemma equalizer_equiv :
  forall
    (E : Ob C) (e1 : Hom E X) (e2 : Hom E X)
    (factorize : forall (E' : Ob C) (e : Hom E' X), e .> f == e .> g -> Hom E' E),
      equalizer C f g E e1 factorize -> equalizer C f g E e2 factorize -> e1 == e2.
Proof.
  intros. edestruct H, H0, (H4 _ _ H3).
  assert (factorize0 E e2 H3 == id E).
    apply H6. cat.
    edestruct (H2 _ _ H3). rewrite H7 in H8. cat.
Qed.

Lemma equalizer_equiv_factorize :
  forall
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E)
    (factorize' : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      equalizer C f g E e factorize -> equalizer C f g E e factorize' ->
        forall (E' : Ob C) (e' : Hom E' X) (H : e' .> f == e' .> g),
          factorize E' e' H == factorize' E' e' H.
Proof.
  intros.
  edestruct H, H3. apply H5.
  edestruct H0, H7. apply H8.
Qed.

Lemma equalizer_is_mono :
  forall
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      equalizer C f g E e factorize -> Mon e.
Proof.
  unfold equalizer, setoid_unique, Mon. intros.
  rename X0 into Z. rename g0 into h'.
  destruct H as [eq H].
  assert ((h .> e) .> f == (h .> e) .> g).
    assocr'. rewrite eq. reflexivity.
  assert ((h' .> e) .> f == (h' .> e) .> g).
    assocr'. rewrite eq. reflexivity.
  destruct (H Z (h .> e) H1) as [u Hh].
  edestruct (H Z (h' .> e) H2) as [u' Hh'].
  assert (factorize0 Z (h .> e) H1 == factorize0 Z (h' .> e) H2).
    rewrite Hh, Hh'. reflexivity. reflexivity. assumption.
  specialize (Hh h); specialize (Hh' h').
  rewrite <- Hh, <- Hh'; try rewrite H3; reflexivity.
Defined.

Lemma equalizer_epi_is_iso :
  forall
    (E : Ob C) (e : Hom E X)
    (factorize : forall (E' : Ob C) (e' : Hom E' X), e' .> f == e' .> g -> Hom E' E),
      equalizer C f g E e factorize -> Epi e -> Iso e.
Proof.
  intros. assert (HMon : Mon e).
    eapply equalizer_is_mono; eauto.
    unfold Epi, Mon in *. destruct H.
    red. pose (Heq := H0 _ _ _ H). assert (id X .> f == id X .> g).
      cat.
      exists (factorize0 _ (id X) H2). split.
        edestruct H1. assert (e .> factorize0 X (id X) H2 .> e == id E .> e).
          assocr. rewrite H3. cat.
          rewrite (HMon _ _ _ H5). reflexivity.
        edestruct H1. apply H3.
Qed.

End HasEqualizers.

Lemma factorize_eq_mor :
  forall [C : Cat] (he : HasEqualizers C) [X Y : Ob C] (f g : Hom X Y),
    factorize (proj1 (is_equalizer X Y f g)) == id (eq_ob f g).
Proof.
  intros. destruct he; cbn in *.
  edestruct is_equalizer0, s. cat.
Defined.

(*
TODO Lemma factorize_comp :
  forall
    (C : Cat) (he : HasEqualizers C)
    (X Y A : Ob C) (f g : Hom X Y)
    (h1 : Hom (eq_ob f g) A) (h2 : Hom A X)
    (H : h1 .> h2 .> f == h1 .> h2 .> g),
      factorize f g _ (h1 .> h2) H ==
(*      id (eq_ob f g).*)
Proof.
  intros. destruct he; cbn in *.
  destruct (is_equalizer0 _ _ f g).
  edestruct is_equalizer0, H1. rewrite H3. reflexivity. reflexivity. cat. apply H3. s. cat.
Defined.
*)