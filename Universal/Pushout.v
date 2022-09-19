From Cat Require Export Cat.

Set Implicit Arguments.

Class isPushout
  (C : Cat) {A B X : Ob C} (f : Hom X A) (g : Hom X B)
  (P : Ob C) (pushl : Hom A P) (pushr : Hom B P)
  (cotriple : forall {P' : Ob C} (pushl' : Hom A P') (pushr' : Hom B P'),
                f .> pushl' == g .> pushr' -> Hom P P')
  : Prop :=
{
  ok : f .> pushl == g .> pushr;
  pushl_cotriple :
    forall (Q : Ob C) (q1 : Hom A Q) (q2 : Hom B Q) (H : f .> q1 == g .> q2),
      pushl .> cotriple q1 q2 H == q1;
  pushr_cotriple :
    forall (Q : Ob C) (q1 : Hom A Q) (q2 : Hom B Q) (H : f .> q1 == g .> q2),
      pushr .> cotriple q1 q2 H == q2;
  equiv_pushout :
    forall (Q : Ob C) (h1 h2 : Hom P Q),
      pushl .> h1 == pushl .> h2 -> pushr .> h1 == pushr .> h2 -> h1 == h2
}.

#[export] Hint Mode isPushout ! ! ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isPushout ! ! ! ! ! - - - - - : core.

Lemma equiv_pushout' :
  forall
    {C : Cat} {A B X : Ob C} {f : Hom X A} {g : Hom X B}
    {P : Ob C} {pushl : Hom A P} {pushr : Hom B P}
    {cotriple : forall {P' : Ob C} (pushl' : Hom A P') (pushr' : Hom B P'),
                  f .> pushl' == g .> pushr' -> Hom P P'}
    {isP : isPushout C f g P pushl pushr (@cotriple)}
    {Y : Ob C} (h1 h2 : Hom P Y),
      h1 == h2 <-> pushl .> h1 == pushl .> h2 /\ pushr .> h1 == pushr .> h2.
Proof.
  split.
  - now intros ->.
  - now intros []; apply equiv_pushout.
Qed.

Section isPushout.

Context
  {C : Cat} {A B X : Ob C} {f : Hom X A} {g : Hom X B}
  {P : Ob C} {pushl : Hom A P} {pushr : Hom B P}
  {cotriple : forall {P' : Ob C} (pushl' : Hom A P') (pushr' : Hom B P'),
                f .> pushl' == g .> pushr' -> Hom P P'}
  {isP : isPushout C f g P pushl pushr (@cotriple)}
  [P' : Ob C] [x : Hom A P'] [y : Hom B P'] [H : f .> x == g .> y].

Arguments cotriple {P'} _ _.

(* #[global] Instance Proper_cotriple :
  Proper (equiv ==> equiv ==> equiv) (@cotriple X).
Proof.
  intros h1 h1' Heq1 h2 h2' Heq2.
  now rewrite equiv_pushout', !pushl_cotriple, !pushr_cotriple.
Defined. *)

Lemma cotriple_universal :
  forall h : Hom P P',
    cotriple x y H == h <-> x == pushl .> h /\ y == pushr .> h.
Proof.
  now intros; rewrite equiv_pushout', pushl_cotriple, pushr_cotriple.
Qed.

Lemma cotriple_unique :
  forall h : Hom P P',
    pushl .> h == x -> pushr .> h == y -> h == cotriple x y H.
Proof.
  now intros; rewrite equiv_pushout', pushl_cotriple, pushr_cotriple.
Qed.

Lemma cotriple_ok :
  cotriple pushl pushr ok == id P.
Proof.
  now rewrite equiv_pushout', pushl_cotriple, pushr_cotriple, !comp_id_r.
Qed.

Lemma cotriple_post :
  forall {Y : Ob C} {h : Hom P' Y},
    exists H' : f .> (x .> h) == g .> (y .> h),
      cotriple (x .> h) (y .> h) H' == cotriple x y H .> h.
Proof.
  esplit. Unshelve. all: cycle 1.
  - now rewrite <- comp_assoc, H, comp_assoc.
  - now rewrite equiv_pushout', pushl_cotriple, pushr_cotriple,
      <- !comp_assoc, pushl_cotriple, pushr_cotriple.
Qed.

End isPushout.

Ltac pushout_simpl :=
  repeat (rewrite
    ?equiv_pushout', ?pushl_cotriple, ?pushr_cotriple, ?cotriple_ok,
    ?comp_id_l, ?comp_id_r, <- ?comp_assoc).

Class HasPushouts (C : Cat) : Type :=
{
  pushout : forall {A B X : Ob C}, Hom X A -> Hom X B -> Ob C;
  pushl : forall {A B X : Ob C} {f : Hom X A} {g : Hom X B}, Hom A (pushout f g);
  pushr : forall {A B X : Ob C} {f : Hom X A} {g : Hom X B}, Hom B (pushout f g);
  cotriple :
    forall
      {A B X : Ob C} {f : Hom X A} {g : Hom X B}
      {P : Ob C} (pushl' : Hom A P) (pushr' : Hom B P),
        f .> pushl' == g .> pushr' -> Hom (pushout f g) P;
  HasPushouts_isPushout :>
    forall {A B X : Ob C} {f : Hom X A} {g : Hom X B},
      isPushout C f g (pushout f g) pushl pushr (@cotriple A B X f g);
}.

Arguments pushout  {C HasPushouts A B X} _ _.
Arguments pushl    {C HasPushouts A B X f g}.
Arguments pushr    {C HasPushouts A B X f g}.
Arguments cotriple {C HasPushouts A B X f g P} _ _ _.

Lemma isPushout_uiso :
  forall
    (C : Cat) (A B X : Ob C) (f : Hom X A) (g : Hom X B)
    (P1 : Ob C) (pushl1 : Hom A P1) (pushr1 : Hom B P1)
    (cotriple1 : forall (P1' : Ob C) (pushl1' : Hom A P1') (pushr1' : Hom B P1'),
                   f .> pushl1' == g .> pushr1' -> Hom P1 P1')
    (P2 : Ob C) (pushl2 : Hom A P2) (pushr2 : Hom B P2)
    (cotriple2 : forall (P2' : Ob C) (pushl2' : Hom A P2') (pushr2' : Hom B P2'),
                   f .> pushl2' == g .> pushr2' -> Hom P2 P2'),
      isPushout C f g P1 pushl1 pushr1 cotriple1 ->
      isPushout C f g P2 pushl2 pushr2 cotriple2 ->
        exists!! f : Hom P2 P1, isIso f /\ pushl1 == pushl2 .> f /\ pushr1 == pushr2 .> f.
Proof.
  intros * H1 H2.
  exists (cotriple2 P1 pushl1 pushr1 ok).
  repeat split.
  - exists (cotriple1 P2 pushl2 pushr2 ok).
    now rewrite !equiv_pushout', <- !comp_assoc, !pushl_cotriple, !pushr_cotriple, !comp_id_r.
  - now rewrite pushl_cotriple.
  - now rewrite pushr_cotriple.
  - intros u (HIso & Heql & Heqr).
    now rewrite equiv_pushout', pushl_cotriple, pushr_cotriple.
Qed.

Lemma isPushout_iso :
  forall
    (C : Cat) (A B X : Ob C) (f : Hom X A) (g : Hom X B)
    (P1 : Ob C) (pushl1 : Hom A P1) (pushr1 : Hom B P1)
    (cotriple1 : forall (P1' : Ob C) (pushl1' : Hom A P1') (pushr1' : Hom B P1'),
                   f .> pushl1' == g .> pushr1' -> Hom P1 P1')
    (P2 : Ob C) (pushl2 : Hom A P2) (pushr2 : Hom B P2)
    (cotriple2 : forall (P2' : Ob C) (pushl2' : Hom A P2') (pushr2' : Hom B P2'),
                   f .> pushl2' == g .> pushr2' -> Hom P2 P2'),
      isPushout C f g P1 pushl1 pushr1 cotriple1 ->
      isPushout C f g P2 pushl2 pushr2 cotriple2 ->
        P1 ~ P2.
Proof.
  intros. destruct (isPushout_uiso H H0).
  symmetry. cat.
Qed.

(*

Lemma isCoproduct_isPushout :
  forall
    (C : Cat) (ht : HasInit C) (A B : Ob C)
    (P : Ob C) (pushl : Hom A P) (pushr : Hom B P)
    (copair : forall (P' : Ob C) (f : Hom A P') (g : Hom B P'), Hom P P'),
      isPushout C (create A) (create B) P pushl pushr (fun P' f g _ => copair P' f g) ->
        isCoproduct C P pushl pushr copair.
Proof.
  red; intros. edestruct H, (H1 _ f g) as [[H2 H3] H4].
    init.
    repeat split.
      now rewrite H2.
      now rewrite H3.
      intros. apply H4. now cat; [rewrite H5 | rewrite H6].
Qed.

Lemma isPushout_isCoproduct :
  forall
    (C : Cat) (ht : HasInit C) (A B : Ob C)
    (P : Ob C) (pushl : Hom A P) (pushr : Hom B P)
    (copair : forall (P' : Ob C) (f : Hom A P') (g : Hom B P'), Hom P P'),
      isCoproduct C P pushl pushr copair ->
        isPushout C (create A) (create B) P pushl pushr (fun P' f g _ => copair P' f g).
Proof.
  red; intros. repeat split.
    init.
    edestruct H, H1. now rewrite <- H3.
    edestruct H, H1. now rewrite <- H4.
    intros. edestruct H. apply H3. cat.
      now rewrite H1.
      now rewrite H5.
Qed.

Lemma isCoequalizer_isPushout :
  forall
    (C : Cat) (A B : Ob C) (f g : Hom A B)
    (P : Ob C) (p : Hom B P)
    (cotriple : forall (P' : Ob C) (f : Hom B P') (g : Hom B P'), Hom P P'),
      isPushout C f g P p p (fun P' f g _ => cotriple P' f g) ->
        isCoequalizer C f g P p (fun (P' : Ob C) (p : Hom B P') _ => cotriple P' p p).
Proof.
  repeat split.
    now destruct H.
    now edestruct H, (H2 _ _ _ H0), H3.
    intros. edestruct H, (H3 _ _ _ H0). apply H5. cat.
Qed.

*)

Definition commutator
  {C : Cat} {hp : HasPushouts C} {A B Γ : Ob C} {f : Hom Γ A} {g : Hom Γ B}
  : Hom (pushout f g) (pushout g f)
  := cotriple pushr pushl (symmetry ok).

Lemma commutator_idem :
  forall {C : Cat} {hp : HasPushouts C} {A B Γ : Ob C} {f : Hom Γ A} {g : Hom Γ B},
    commutator .> commutator == id (pushout f g).
Proof.
  unfold commutator; intros.
  apply equiv_pushout.
  - now rewrite <- comp_assoc, pushl_cotriple, pushr_cotriple, comp_id_r.
  - now rewrite <- comp_assoc, pushr_cotriple, pushl_cotriple, comp_id_r.
Qed.

Lemma isIso_commutator :
  forall {C : Cat} {hp : HasPushouts C} {A B Γ : Ob C} {f : Hom Γ A} {g : Hom Γ B},
    isIso (commutator (f := f) (g := g)).
Proof.
  red; intros.
  exists commutator.
  split; apply commutator_idem.
Qed.

Lemma pushout_comm :
  forall {C : Cat} {hp : HasPushouts C} {A B Γ : Ob C} {f : Hom Γ A} {g : Hom Γ B},
    pushout f g ~ pushout g f.
Proof.
  red; intros.
  exists commutator.
  now apply isIso_commutator.
Qed.