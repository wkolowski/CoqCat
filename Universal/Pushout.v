From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Coproduct Coequalizer.

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

Lemma comp_cotriple :
  forall {Y : Ob C} {h : Hom P' Y},
    cotriple x y H .> h == cotriple (x .> h) (y .> h) (wut_r h H).
Proof.
  now intros; rewrite equiv_pushout', <- !comp_assoc, !pushl_cotriple, !pushr_cotriple.
Qed.

End isPushout.

Ltac pushout_simpl :=
  repeat (rewrite
    ?comp_cotriple, ?equiv_pushout', ?pushl_cotriple, ?pushr_cotriple, ?cotriple_ok,
    ?comp_id_l, ?comp_id_r, <- ?comp_assoc).

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
        exists!! f : Hom P1 P2, isIso f /\ pushl2 == pushl1 .> f /\ pushr2 == pushr1 .> f.
Proof.
  intros * H1 H2.
  exists (cotriple1 P2 pushl2 pushr2 ok).
  repeat split.
  - exists (cotriple2 P1 pushl1 pushr1 ok).
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
  now intros * H1 H2; destruct (isPushout_uiso H1 H2) as [i []]; exists i.
Qed.

Section Pushout_lemmas.

Context
  {C : Cat} {A B X : Ob C} {f : Hom X A} {g : Hom X B}
  {P : Ob C} {pushl : Hom A P} {pushr : Hom B P}
  {cotriple : forall {P' : Ob C} (a : Hom A P') (b : Hom B P'), f .> a == g .> b -> Hom P P'}
  {HisP : isPushout C f g P pushl pushr (@cotriple)}.

Lemma isEpi_pushl :
  isEpi g -> isEpi pushl.
Proof.
  unfold isEpi; intros * H Y h1 h2 Heq.
  apply equiv_pushout; [easy |].
  apply H.
  now rewrite <- comp_assoc, <- ok, comp_assoc, Heq, <- comp_assoc, ok.
Qed.

Lemma isEpi_pushr :
  isEpi f -> isEpi pushr.
Proof.
  unfold isEpi; intros * H Y h1 h2 Heq.
  apply equiv_pushout; [| easy].
  apply H.
  now rewrite <- comp_assoc, ok, comp_assoc, Heq, <- comp_assoc, <- ok.
Qed.

Lemma isIso_pushl :
  isIso g -> isIso pushl.
Proof.
  unfold isIso; intros (g' & Heq1 & Heq2).
  unshelve esplit.
  - apply (cotriple A (id A) (g' .> f)).
    abstract (now rewrite <- comp_assoc, Heq1, comp_id_l, comp_id_r).
  - now pushout_simpl; rewrite comp_assoc, ok, <- comp_assoc, Heq2.
Qed.

Lemma isIso_pushr :
  isIso f -> isIso pushr.
Proof.
  unfold isIso; intros (f' & Heq1 & Heq2).
  unshelve esplit.
  - apply (cotriple B (f' .> g) (id B)).
    abstract (now rewrite <- comp_assoc, Heq1, comp_id_l, comp_id_r).
  - now pushout_simpl; rewrite comp_assoc, <- ok, <- comp_assoc, Heq2.
Qed.

End Pushout_lemmas.

Lemma isPushout_id_l :
  forall {C : Cat} {A B : Ob C} {g : Hom A B},
    isPushout C (id A) g B g (id B) (fun Γ _ b _ => b).
Proof.
  split.
  - now rewrite comp_id_l, comp_id_r.
  - now intros; rewrite <- H, comp_id_l.
  - now intros; rewrite comp_id_l.
  - now intros; rewrite !comp_id_l in H0.
Qed.

Lemma isPushout_id_r :
  forall {C : Cat} {A B : Ob C} (f : Hom B A),
    isPushout C f (id B) A (id A) f (fun Γ a _ _ => a).
Proof.
  split.
  - now rewrite comp_id_l, comp_id_r.
  - now intros; rewrite comp_id_l.
  - now intros; rewrite H, comp_id_l.
  - now intros; rewrite !comp_id_l in H.
Qed.

Lemma isPushout_comp :
  forall
    {C : Cat} {A A' B Γ : Ob C} {f : Hom Γ A} {g : Hom Γ B} {h : Hom A A'}
    {P : Ob C} {pushl : Hom A P} {pushr : Hom B P}
    {cotriple : forall {X : Ob C} (pushl' : Hom A X) (pushr' : Hom B X),
      f .> pushl' == g .> pushr' -> Hom P X}
    (HisP : isPushout C f g P pushl pushr (@cotriple))
    {Q : Ob C} {pushl' : Hom A' Q} {pushr' : Hom P Q}
    {cotriple' : forall {X : Ob C} (pushl'' : Hom A' X) (pushr'' : Hom P X),
      h .> pushl'' == pushl .> pushr'' -> Hom Q X}
    (HisQ : isPushout C h pushl Q pushl' pushr' (@cotriple')),
      isPushout C (f .> h) g Q pushl' (pushr .> pushr')
        (fun X h1 h2 Heq => cotriple' h1 (cotriple (h .> h1) h2 (assoc_l Heq))
          ltac:(now rewrite pushl_cotriple)).
Proof.
  split.
  - now rewrite comp_assoc, ok, <- !comp_assoc, ok.
  - now intros; rewrite pushl_cotriple.
  - now intros; rewrite comp_assoc, !pushr_cotriple.
  - intros * Heq1 Heq2.
    rewrite !equiv_pushout'.
    repeat split; [easy | |].
    + now rewrite <- !comp_assoc, <- ok, !comp_assoc, Heq1.
    + now rewrite <- !comp_assoc, Heq2.
Qed.

Lemma isCoproduct_isPushout :
  forall
    (C : Cat) (ht : HasInit C) (A B : Ob C)
    (P : Ob C) (pushl : Hom A P) (pushr : Hom B P)
    (cotriple : forall {P' : Ob C} (f : Hom A P') (g : Hom B P'),
      create A .> f == create B .> g -> Hom P P'),
      isPushout C (create A) (create B) P pushl pushr (@cotriple) ->
        isCoproduct C P pushl pushr (fun P' h1 h2 => cotriple h1 h2 (equiv_initial _)).
Proof.
  split; intros.
  - now rewrite pushl_cotriple.
  - now rewrite pushr_cotriple.
  - now apply equiv_pushout.
Qed.

Lemma isPushout_isCoproduct :
  forall
    (C : Cat) (ht : HasInit C) (A B : Ob C)
    (P : Ob C) (finl : Hom A P) (finr : Hom B P)
    (copair : forall (P' : Ob C) (f : Hom A P') (g : Hom B P'), Hom P P'),
      isCoproduct C P finl finr copair ->
        isPushout C (create A) (create B) P finl finr (fun P' f g _ => copair P' f g).
Proof.
  split; intros.
  - now apply equiv_initial.
  - now apply finl_copair.
  - now apply finr_copair.
  - now apply equiv_coproduct.
Qed.

Lemma isPushout_isCoproduct' :
  forall
    (C : Cat) (ht : HasInit C) (A B : Ob C)
    (P : Ob C) (finl : Hom A P) (finr : Hom B P)
    (copair : forall (P' : Ob C) (f : Hom A P') (g : Hom B P'), Hom P P'),
      isCoproduct C P finl finr copair
        <->
      isPushout C (create A) (create B) P finl finr (fun P' f g _ => copair P' f g).
Proof.
  split.
  - split; intros.
    + now apply equiv_initial.
    + now intros; apply finl_copair.
    + now intros; apply finr_copair.
    + now intros; apply equiv_coproduct.
  - split; intros.
    + rewrite (pushl_cotriple (isPushout := H)); [easy |].
      now apply equiv_initial.
    + rewrite (pushr_cotriple (isPushout := H)); [easy |].
      now apply equiv_initial.
    + now apply equiv_pushout.
Qed.

Lemma isCoequalizer_isPushout :
  forall
    (C : Cat) (A B : Ob C) (f g : Hom A B)
    (P : Ob C) (push : Hom B P)
    (cotriple : forall (P' : Ob C) (pushl' pushr' : Hom B P'),
      f .> pushl' == g .> pushr' -> Hom P P'),
      isPushout C f g P push push cotriple ->
        isCoequalizer C f g P push (fun Q q Heq => cotriple Q q q Heq).
Proof.
  split; intros.
  - now apply ok.
  - now apply pushl_cotriple.
  - now apply equiv_pushout.
Qed.

Lemma isCoequalizer_isPushout' :
  forall
    (C : Cat) (A B Γ : Ob C) (f : Hom Γ A) (g : Hom Γ B)
    (P : Ob C) (pushl : Hom A P) (pushr : Hom B P)
    (cotriple : forall (P' : Ob C) (pushl' : Hom A P') (pushr' : Hom B P'),
      f .> pushl' == g .> pushr' -> Hom P P'),
      isPushout C f g P pushl pushr cotriple ->
        isCoequalizer C (f .> pushl) (g .> pushr) P (id P)
          (fun Q' q Heq => cotriple _ (pushl .> q) (pushr .> q)
            ltac:(now rewrite <- !comp_assoc)).
Proof.
  split.
  - now rewrite ok.
  - now intros; rewrite equiv_pushout', comp_id_l, pushl_cotriple, pushr_cotriple.
  - now intros * Heq; rewrite !comp_id_l in Heq.
Qed.

Lemma isPushout_isCoequalizer_isCoproduct :
  forall
    (C : Cat) (A B Γ : Ob C) (f : Hom Γ A) (g : Hom Γ B)
    (AB : Ob C) (finl : Hom A AB) (finr : Hom B AB)
    (copair : forall {X : Ob C} (finl' : Hom A X) (finr' : Hom B X), Hom AB X)
    (HisCop : isCoproduct C AB finl finr (@copair))
    (Q : Ob C) (coequalize : Hom AB Q)
    (cofactorize : forall {Q' : Ob C} (q : Hom AB Q'),
      (f .> finl) .> q == (g .> finr) .> q -> Hom Q Q')
    (HisCoeq : isCoequalizer C (f .> finl) (g .> finr) Q coequalize (@cofactorize)),
      isPushout C f g Q (finl .> coequalize) (finr .> coequalize)
        (fun P' pushl' pushr' Heq => cofactorize (copair pushl' pushr')
          ltac:(now rewrite !comp_assoc, finl_copair, finr_copair)).
Proof.
  split.
  - now rewrite <- !comp_assoc, Coequalizer.ok.
  - now intros; rewrite comp_assoc, coequalize_cofactorize, finl_copair.
  - now intros; rewrite comp_assoc, coequalize_cofactorize, finr_copair.
  - now intros; rewrite equiv_coequalizer', equiv_coproduct', <- !comp_assoc.
Qed.

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
  now split; apply commutator_idem.
Qed.

Lemma pushout_comm :
  forall {C : Cat} {hp : HasPushouts C} {A B Γ : Ob C} {f : Hom Γ A} {g : Hom Γ B},
    pushout f g ~ pushout g f.
Proof.
  red; intros.
  exists commutator.
  now apply isIso_commutator.
Qed.

#[refine]
#[local]
Instance HasPushouts_HasCoproducts_HasCoequalizers
  {C : Cat} (hp : HasCoproducts C) (he : HasCoequalizers C) : HasPushouts C :=
{
  pushout  := fun A B Γ f g => @coequalizer _ _ Γ (coproduct A B) (f .> finl) (g .> finr);
  pushl    := fun A B Γ f g => finl .> coequalize (f .> finl) (g .> finr);
  pushr    := fun A B Γ f g => finr .> coequalize (f .> finl) (g .> finr);
  cotriple := fun A B Γ f g X h1 h2 Heq => cofactorize (copair h1 h2) _;
}.
Proof.
  - now rewrite  !comp_assoc, finl_copair, finr_copair.
  - split; intros.
    + now rewrite <- !comp_assoc, Coequalizer.ok.
    + now rewrite comp_assoc, coequalize_cofactorize, finl_copair.
    + now rewrite comp_assoc, coequalize_cofactorize, finr_copair.
    + now rewrite equiv_coequalizer', equiv_coproduct', <- !comp_assoc.
Defined.