From Cat Require Export Cat.

Set Implicit Arguments.

Class isPushout
  (C : Cat) {A B X : Ob C} (f : Hom X A) (g : Hom X B)
  (P : Ob C) (pushl : Hom A P) (pushr : Hom B P)
  (cofactor : forall {P' : Ob C} (pushl' : Hom A P') (pushr' : Hom B P'),
                f .> pushl' == g .> pushr' -> Hom P P')
  : Prop :=
{
  pushout_ok : f .> pushl == g .> pushr;
  pushl_cofactor :
    forall (Q : Ob C) (q1 : Hom A Q) (q2 : Hom B Q) (H : f .> q1 == g .> q2),
      pushl .> cofactor q1 q2 H == q1;
  pushr_cofactor :
    forall (Q : Ob C) (q1 : Hom A Q) (q2 : Hom B Q) (H : f .> q1 == g .> q2),
      pushr .> cofactor q1 q2 H == q2;
  cofactor_equiv :
    forall (Q : Ob C) (h1 h2 : Hom P Q),
      pushl .> h1 == pushl .> h2 -> pushr .> h1 == pushr .> h2 -> h1 == h2
}.

#[export] Hint Mode isPushout ! ! ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isPushout ! ! ! - - - - - - - : core.

Class HasPushouts (C : Cat) : Type :=
{
  pushoutOb : forall {A B X : Ob C}, Hom X A -> Hom X B -> Ob C;
  pushl : forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom A (pushoutOb f g);
  pushr : forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom B (pushoutOb f g);
  cofactor :
    forall
      {A B X : Ob C} (f : Hom X A) (g : Hom X B)
      {P : Ob C} (pushl' : Hom A P) (pushr' : Hom B P),
        f .> pushl' == g .> pushr' -> Hom (pushoutOb f g) P;
  HasPushouts_isPushout :>
    forall {A B X : Ob C} {f : Hom X A} {g : Hom X B},
      isPushout C f g (pushoutOb f g) (pushl f g) (pushr f g) (@cofactor A B X f g);
  (* Proper_pushoutOb :
    forall (A B X : Ob C) (f f' : Hom X A) (g g' : Hom X B),
      f == f' -> g == g' -> JMequiv (id (pushoutOb f g)) (id (pushoutOb f' g'));
  Proper_pushl :
    forall (A B X : Ob C) (f f' : Hom X A) (g g' : Hom X B),
      f == f' -> g == g' -> JMequiv (pushl f g) (pushl f' g');
  Proper_pushr :
    forall (A B X : Ob C) (f f' : Hom X A) (g g' : Hom X B),
      f == f' -> g == g' -> JMequiv (pushr f g) (pushr f' g'); *)
}.

Arguments pushoutOb {C HasPushouts A B X} _ _.
Arguments pushl     {C HasPushouts A B X f g}.
Arguments pushr     {C HasPushouts A B X f g}.
Arguments cofactor  {C HasPushouts A B X f g P pushl' pushr'} _.

Lemma cofactor_equiv' :
  forall
    {C : Cat} {A B X : Ob C} {f : Hom X A} {g : Hom X B}
    {P : Ob C} {pushl : Hom A P} {pushr : Hom B P}
    {cofactor : forall {P' : Ob C} (pushl' : Hom A P') (pushr' : Hom B P'),
                  f .> pushl' == g .> pushr' -> Hom P P'}
    {isP : isPushout C f g P pushl pushr (@cofactor)}
    {Y : Ob C} (h1 h2 : Hom P Y),
      h1 == h2 <-> pushl .> h1 == pushl .> h2 /\ pushr .> h1 == pushr .> h2.
Proof.
  split.
  - now intros ->.
  - now intros []; apply cofactor_equiv.
Qed.

Section isPushout.

Context
  {C : Cat} {A B X : Ob C} {f : Hom X A} {g : Hom X B}
  {P : Ob C} {pushl : Hom A P} {pushr : Hom B P}
  {cofactor : forall {P' : Ob C} (pushl' : Hom A P') (pushr' : Hom B P'),
                f .> pushl' == g .> pushr' -> Hom P P'}
  {isP : isPushout C f g P pushl pushr (@cofactor)}
  [P' : Ob C] [x : Hom A P'] [y : Hom B P'] [H : f .> x == g .> y].

Arguments cofactor {P'} _ _.

(* #[global] Instance Proper_cofactor :
  Proper (equiv ==> equiv ==> equiv) (@cofactor X).
Proof.
  intros h1 h1' Heq1 h2 h2' Heq2.
  now rewrite cofactor_equiv', !pushl_cofactor, !pushr_cofactor.
Defined. *)

Lemma cofactor_universal :
  forall h : Hom P P',
    cofactor x y H == h <-> x == pushl .> h /\ y == pushr .> h.
Proof.
  now intros; rewrite cofactor_equiv', pushl_cofactor, pushr_cofactor.
Qed.

Lemma cofactor_unique :
  forall h : Hom P P',
    pushl .> h == x -> pushr .> h == y -> h == cofactor x y H.
Proof.
  now intros; rewrite cofactor_equiv', pushl_cofactor, pushr_cofactor.
Qed.

Lemma cofactor_id :
  cofactor pushl pushr pushout_ok == id P.
Proof.
  now rewrite cofactor_equiv', pushl_cofactor, pushr_cofactor, !comp_id_r.
Qed.

Lemma cofactor_post :
  forall {Y : Ob C} {h : Hom P' Y},
    exists H' : f .> (x .> h) == g .> (y .> h),
      cofactor (x .> h) (y .> h) H' == cofactor x y H .> h.
Proof.
  esplit. Unshelve. all: cycle 1.
  - now rewrite <- comp_assoc, H, comp_assoc.
  - now rewrite cofactor_equiv', pushl_cofactor, pushr_cofactor,
      <- !comp_assoc, pushl_cofactor, pushr_cofactor.
Qed.

End isPushout.

Lemma isPushout_uiso :
  forall
    (C : Cat) (A B X : Ob C) (f : Hom X A) (g : Hom X B)
    (P1 : Ob C) (pushl1 : Hom A P1) (pushr1 : Hom B P1)
    (cofactor1 : forall (P1' : Ob C) (pushl1' : Hom A P1') (pushr1' : Hom B P1'),
                   f .> pushl1' == g .> pushr1' -> Hom P1 P1')
    (P2 : Ob C) (pushl2 : Hom A P2) (pushr2 : Hom B P2)
    (cofactor2 : forall (P2' : Ob C) (pushl2' : Hom A P2') (pushr2' : Hom B P2'),
                   f .> pushl2' == g .> pushr2' -> Hom P2 P2'),
      isPushout C f g P1 pushl1 pushr1 cofactor1 ->
      isPushout C f g P2 pushl2 pushr2 cofactor2 ->
        exists!! f : Hom P2 P1, isIso f /\ pushl1 == pushl2 .> f /\ pushr1 == pushr2 .> f.
Proof.
  intros * H1 H2.
  exists (cofactor2 P1 pushl1 pushr1 pushout_ok).
  repeat split.
  - exists (cofactor1 P2 pushl2 pushr2 pushout_ok).
    now rewrite !cofactor_equiv', <- !comp_assoc, !pushl_cofactor, !pushr_cofactor, !comp_id_r.
  - now rewrite pushl_cofactor.
  - now rewrite pushr_cofactor.
  - intros u (HIso & Heql & Heqr).
    now rewrite cofactor_equiv', pushl_cofactor, pushr_cofactor.
Qed.

Lemma isPushout_iso :
  forall
    (C : Cat) (A B X : Ob C) (f : Hom X A) (g : Hom X B)
    (P1 : Ob C) (pushl1 : Hom A P1) (pushr1 : Hom B P1)
    (cofactor1 : forall (P1' : Ob C) (pushl1' : Hom A P1') (pushr1' : Hom B P1'),
                   f .> pushl1' == g .> pushr1' -> Hom P1 P1')
    (P2 : Ob C) (pushl2 : Hom A P2) (pushr2 : Hom B P2)
    (cofactor2 : forall (P2' : Ob C) (pushl2' : Hom A P2') (pushr2' : Hom B P2'),
                   f .> pushl2' == g .> pushr2' -> Hom P2 P2'),
      isPushout C f g P1 pushl1 pushr1 cofactor1 ->
      isPushout C f g P2 pushl2 pushr2 cofactor2 ->
        P1 ~ P2.
Proof.
  intros. destruct (isPushout_uiso H H0).
  symmetry. cat.
Qed.

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
      rewrite H2. reflexivity.
      rewrite H3. reflexivity.
      intros. apply H4. cat; [rewrite H5 | rewrite H6]; reflexivity.
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
    edestruct H, H1. rewrite <- H3. reflexivity.
    edestruct H, H1. rewrite <- H4. reflexivity.
    intros. edestruct H. apply H3. cat.
      rewrite H1. reflexivity.
      rewrite H5. reflexivity.
Qed.

Lemma isCoequalizer_isPushout :
  forall
    (C : Cat) (A B : Ob C) (f g : Hom A B)
    (P : Ob C) (p : Hom B P)
    (cofactor : forall (P' : Ob C) (f : Hom B P') (g : Hom B P'), Hom P P'),
      isPushout C f g P p p (fun P' f g _ => cofactor P' f g) ->
        isCoequalizer C f g P p (fun (P' : Ob C) (p : Hom B P') _ => cofactor P' p p).
Proof.
  repeat split.
    destruct H. assumption.
    edestruct H, (H2 _ _ _ H0), H3. assumption.
    intros. edestruct H, (H3 _ _ _ H0). apply H5. cat.
Qed.


