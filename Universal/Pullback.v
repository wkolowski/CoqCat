From Cat Require Import Cat.
From Cat.Universal Require Import Initial Terminal Product Equalizer.

Set Implicit Arguments.

Class isPullback
  (C : Cat) {A B X : Ob C} (f : Hom A X) (g : Hom B X)
  (P : Ob C) (pullL : Hom P A) (pullR : Hom P B)
  (triple : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P)
  : Prop :=
{
  ok : pullL .> f == pullR .> g;
  triple_pullL :
    forall (Γ : Ob C) (a : Hom Γ A) (b : Hom Γ B) (H : a .> f == b .> g),
      triple a b H .> pullL == a;
  triple_pullR :
    forall (Γ : Ob C) (a : Hom Γ A) (b : Hom Γ B) (H : a .> f == b .> g),
      triple a b H .> pullR == b;
  equiv_pullback :
    forall (Γ : Ob C) (x y : Hom Γ P),
      x .> pullL == y .> pullL -> x .> pullR == y .> pullR -> x == y;
}.

#[export] Hint Mode isPullback ! ! ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isPullback ! ! ! ! ! - - - - - : core.

Lemma equiv_pullback' :
  forall
    {C : Cat} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
    {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
    {triple : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P}
    {isP : isPullback C f g P pullL pullR (@triple)}
    {Γ : Ob C} (x y : Hom Γ P),
      x == y <-> x .> pullL == y .> pullL /\ x .> pullR == y .> pullR.
Proof.
  split.
  - now intros ->.
  - now intros []; apply equiv_pullback.
Qed.

Section isPullback.

Context
  {C : Cat} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
  {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
  {triple : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P}
  {isP : isPullback C f g P pullL pullR (@triple)}
  [Γ : Ob C] [a : Hom Γ A] [b : Hom Γ B] [H : a .> f == b .> g].

Arguments triple {Γ} _ _.

Lemma triple_universal :
  forall h : Hom Γ P,
    triple a b H == h <-> a == h .> pullL /\ b == h .> pullR.
Proof.
  now intros; rewrite equiv_pullback', triple_pullL, triple_pullR.
Qed.

Lemma triple_unique :
  forall h : Hom Γ P,
    h .> pullL == a -> h .> pullR == b -> h == triple a b H.
Proof.
  now intros; rewrite equiv_pullback', triple_pullL, triple_pullR.
Qed.

Lemma triple_ok :
  triple pullL pullR ok == id P.
Proof.
  now rewrite equiv_pullback', triple_pullL, triple_pullR, !comp_id_l.
Qed.

Lemma comp_triple :
  forall {Y : Ob C} {h : Hom Y Γ},
    h .> triple a b H == triple (h .> a) (h .> b) (wut_l h H).
Proof.
  now intros; rewrite equiv_pullback', !comp_assoc, !triple_pullL, !triple_pullR.
Qed.

End isPullback.

Ltac pullback_simpl :=
  repeat (rewrite
    ?comp_triple, ?equiv_pullback', ?triple_pullL, ?triple_pullR, ?triple_ok,
    ?comp_id_l, ?comp_id_r, ?comp_assoc).

Lemma isPullback_uiso :
  forall
    (C : Cat) (A B X : Ob C) (f : Hom A X) (g : Hom B X)
    (P1 : Ob C) (pullL1 : Hom P1 A) (pullR1 : Hom P1 B)
    (triple1 : forall (Γ : Ob C) (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P1)
    (P2 : Ob C) (pullL2 : Hom P2 A) (pullR2 : Hom P2 B)
    (triple2 : forall (Γ : Ob C) (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P2),
      isPullback C f g P1 pullL1 pullR1 triple1 ->
      isPullback C f g P2 pullL2 pullR2 triple2 ->
        exists!! f : Hom P1 P2, isIso f /\ f .> pullL2 == pullL1 /\ f .> pullR2 == pullR1.
Proof.
  intros * H1 H2.
  exists (triple2 _ pullL1 pullR1 ok).
  repeat split.
  - exists (triple1 P2 pullL2 pullR2 ok).
    now rewrite !equiv_pullback', !comp_assoc, !triple_pullL, !triple_pullR, !comp_id_l.
  - now rewrite triple_pullL.
  - now rewrite triple_pullR.
  - intros u (HIso & Heql & Heqr).
    now rewrite equiv_pullback', triple_pullL, triple_pullR.
Qed.

Lemma isPullback_iso :
  forall
    (C : Cat) (A B X : Ob C) (f : Hom A X) (g : Hom B X)
    (P1 : Ob C) (pullL1 : Hom P1 A) (pullR1 : Hom P1 B)
    (triple1 : forall (Γ : Ob C) (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P1)
    (P2 : Ob C) (pullL2 : Hom P2 A) (pullR2 : Hom P2 B)
    (triple2 : forall (Γ : Ob C) (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P2),
      isPullback C f g P1 pullL1 pullR1 triple1 ->
      isPullback C f g P2 pullL2 pullR2 triple2 ->
        P1 ~ P2.
Proof.
  now intros * H1 H2; destruct (isPullback_uiso H1 H2) as [i []]; exists i.
Qed.

Section Pullback_lemmas.

Context
  {C : Cat} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
  {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
  {triple : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P}
  {HisP : isPullback C f g P pullL pullR (@triple)}.

Lemma isMono_pullL :
  isMono g -> isMono pullL.
Proof.
  unfold isMono; intros H Y h1 h2 Heq.
  apply equiv_pullback; [easy |].
  apply H.
  now rewrite !comp_assoc, <- ok, <- !comp_assoc, Heq.
Qed.

Lemma isMono_pullR :
  isMono f -> isMono pullR.
Proof.
  unfold isMono; intros * H Y h1 h2 Heq.
  apply equiv_pullback; [| easy].
  apply H.
  now rewrite !comp_assoc, ok, <- !comp_assoc, Heq.
Qed.

Lemma isIso_pullL :
  isIso g -> isIso pullL.
Proof.
  unfold isIso; intros (g' & Heq1 & Heq2).
  unshelve esplit.
  - apply (triple A (id A) (f .> g')).
    abstract (now rewrite comp_assoc, Heq2, comp_id_l, comp_id_r).
  - pullback_simpl; repeat split; [easy | | easy].
    now rewrite <- comp_assoc, ok, comp_assoc, Heq1, comp_id_r.
Qed.

Lemma isIso_pullR :
  isIso f -> isIso pullR.
Proof.
  unfold isIso; intros (f' & Heq1 & Heq2).
  unshelve esplit.
  - apply (triple B (g .> f') (id B)).
    abstract (now rewrite comp_assoc, Heq2, comp_id_l, comp_id_r).
  - pullback_simpl; repeat split; [| easy | easy].
    now rewrite <- comp_assoc, <- ok, comp_assoc, Heq1, comp_id_r.
Qed.

End Pullback_lemmas.

Lemma isPullback_id_l :
  forall {C : Cat} {A B : Ob C} (g : Hom B A),
    isPullback C (id A) g B g (id B) (fun Γ _ b _ => b).
Proof.
  split; intros.
  - now rewrite comp_id_l, comp_id_r.
  - now rewrite <- H, comp_id_r.
  - now rewrite comp_id_r.
  - now rewrite !comp_id_r in H0.
Qed.

Lemma isPullback_id_r :
  forall {C : Cat} {A B : Ob C} (f : Hom A B),
    isPullback C f (id B) A (id A) f (fun Γ a _ _ => a).
Proof.
  split; intros.
  - now rewrite comp_id_l, comp_id_r.
  - now rewrite comp_id_r.
  - now rewrite H, comp_id_r.
  - now rewrite !comp_id_r in H.
Qed.

Lemma isPullback_comp :
  forall
    {C : Cat} {A A' B X : Ob C} {f : Hom A X} {g : Hom B X} {h : Hom A' A}
    {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
    {triple : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P}
    (HisP : isPullback C f g P pullL pullR (@triple))
    {Q : Ob C} {pullL' : Hom Q A'} {pullR' : Hom Q P}
    {triple' : forall {Γ : Ob C} (a : Hom Γ A') (b : Hom Γ P), a .> h == b .> pullL -> Hom Γ Q}
    (HisQ : isPullback C h pullL Q pullL' pullR' (@triple')),
      isPullback C (h .> f) g Q pullL' (pullR' .> pullR)
        (fun Γ x y H => triple' x (triple (x .> h) y (unassoc_l H)) ltac:(now rewrite triple_pullL)).
Proof.
  split.
  - now rewrite <- comp_assoc, ok, !comp_assoc, ok.
  - now intros; rewrite triple_pullL.
  - now intros; rewrite <- comp_assoc, !triple_pullR.
  - intros * Heq1 Heq2.
    rewrite !equiv_pullback'.
    repeat split; [easy | |].
    + now rewrite !comp_assoc, <- ok, <- !comp_assoc, Heq1.
    + now rewrite !comp_assoc, Heq2.
Qed.

Lemma isPullback_comp' :
  forall
    {C : Cat} {A A' B X : Ob C} {f : Hom A X} {g : Hom B X} {h : Hom A' A}
    {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
    {triple : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P}
    (HisP : isPullback C f g P pullL pullR (@triple))
    {Q : Ob C} {pullL' : Hom Q A'} {pullR' : Hom Q P}
    {triple' : forall {Γ : Ob C} (a' : Hom Γ A') (b : Hom Γ P), a' .> h == b .> pullL -> Hom Γ Q},
      isPullback C (h .> f) g Q pullL' (pullR' .> pullR)
        (fun Γ a' b H =>
          triple' a' (triple (a' .> h) b (unassoc_l H)) ltac:(now rewrite triple_pullL)) ->
        isPullback C h pullL Q pullL' pullR' (@triple').
Proof.
  intros * HisP; split.
  - admit.
  - intros Γ a' b Heq; destruct HisP.
    assert (Heq' : a' .> (h .> f) == (b .> pullR) .> g).
    {
      now rewrite <- comp_assoc, Heq, comp_assoc, ok.
    }
    rewrite <- (triple_pullL0 Γ a' (b .> pullR) Heq') at 2.
    assert (Heq'' : b == triple Γ (a' .> h) (b .> pullR) (unassoc_l Heq')).
    {
      apply equiv_pullback.
      - now rewrite <- Heq, triple_pullL.
      - now rewrite triple_pullR.
    }
    admit.
  - admit.
Abort.

Lemma isProduct_isPullback :
  forall
    (C : Cat) (ht : HasTerm C) (A B : Ob C)
    (P : Ob C) (pullL : Hom P A) (pullR : Hom P B)
    (triple : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B),
      a .> delete A == b .> delete B -> Hom Γ P),
      isPullback C (delete A) (delete B) P pullL pullR (@triple) ->
        isProduct C P pullL pullR (fun Γ a b => triple a b (equiv_terminal _)).
Proof.
  split; intros.
  - now rewrite triple_pullL.
  - now rewrite triple_pullR.
  - now apply equiv_pullback.
Qed.

Lemma isPullback_isProduct :
  forall
    (C : Cat) (ht : HasTerm C) (A B : Ob C)
    (P : Ob C) (outl : Hom P A) (outr : Hom P B)
    (fpair : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ P),
      isProduct C P outl outr (@fpair) ->
        isPullback C (delete A) (delete B) P outl outr (fun Γ a b _ => fpair a b).
Proof.
  split; intros.
  - now apply equiv_terminal.
  - now rewrite fpair_outl.
  - now rewrite fpair_outr.
  - now apply equiv_product.
Qed.

Lemma isPullback_isProduct' :
  forall
    (C : Cat) (ht : HasTerm C) (A B : Ob C)
    (P : Ob C) (outl : Hom P A) (outr : Hom P B)
    (fpair : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ P),
      isProduct C P outl outr (@fpair)
        <->
      isPullback C (delete A) (delete B) P outl outr (fun Γ a b _ => fpair a b).
Proof.
  split.
  - split; intros.
    + now apply equiv_terminal.
    + now rewrite fpair_outl.
    + now rewrite fpair_outr.
    + now apply equiv_product.
  - split; intros.
    + rewrite (triple_pullL (isPullback := H)); [easy |].
      now apply equiv_terminal.
    + rewrite (triple_pullR (isPullback := H)); [easy |].
      now apply equiv_terminal.
    + now apply equiv_pullback.
Qed.

Lemma isEqualizer_isPullback
  (C : Cat) (A X : Ob C) (f g : Hom A X)
  (P : Ob C) (pull : Hom P A)
  (triple : forall {Γ : Ob C} (a1 a2 : Hom Γ A), a1 .> f == a2 .> g -> Hom Γ P) :
    isPullback C f g P pull pull (@triple) ->
      isEqualizer C f g P pull (fun Γ a Heq => triple a a Heq).
Proof.
  split; intros.
  - now apply ok.
  - now apply triple_pullL.
  - now apply equiv_pullback.
Qed.

Lemma isEqualizer_isPullback'
  (C : Cat) (A B X : Ob C) (f : Hom A X) (g : Hom B X)
  (P : Ob C) (pullL : Hom P A) (pullR : Hom P B)
  (triple : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), a .> f == b .> g -> Hom Γ P) :
    isPullback C f g P pullL pullR (@triple) ->
      isEqualizer C (pullL .> f) (pullR .> g) P (id P)
        (fun Γ x Heq => triple (x .> pullL) (x .> pullR)
            ltac:(now rewrite !comp_assoc)).
Proof.
  split.
  - now rewrite ok.
  - now intros; rewrite equiv_pullback', comp_id_r, triple_pullL, triple_pullR.
  - now intros * Heq; rewrite !comp_id_r in Heq.
Qed.

Lemma isPullback_isEqualizer_isProduct :
  forall
    (C : Cat) (A B X : Ob C) (f : Hom A X) (g : Hom B X)
    (AB : Ob C) (outl : Hom AB A) (outr : Hom AB B)
    (fpair : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ AB)
    (HisP : isProduct C AB outl outr (@fpair))
    (E : Ob C) (equalize : Hom E AB)
    (factorize : forall {E' : Ob C} (e : Hom E' AB),
      e .> (outl .> f) == e .> (outr .> g) -> Hom E' E)
    (HisEq : isEqualizer C (outl .> f) (outr .> g) E equalize (@factorize)),
      isPullback C f g E (equalize .> outl) (equalize .> outr)
        (fun Γ a b Heq => factorize (fpair a b)
          ltac:(now rewrite <- !comp_assoc, fpair_outl, fpair_outr)).
Proof.
  split; intros.
  - now rewrite !comp_assoc, Equalizer.ok.
  - now rewrite <- comp_assoc, factorize_equalize, fpair_outl.
  - now rewrite <- comp_assoc, factorize_equalize, fpair_outr.
  - now rewrite equiv_equalizer', equiv_product', !comp_assoc.
Qed.

Class HasPullbacks (C : Cat) : Type :=
{
  pullback : forall {A B X : Ob C}, Hom A X -> Hom B X -> Ob C;
  pullL : forall {A B X : Ob C} {f : Hom A X} {g : Hom B X}, Hom (pullback f g) A;
  pullR : forall {A B X : Ob C} {f : Hom A X} {g : Hom B X}, Hom (pullback f g) B;
  triple :
    forall {A B X : Ob C} [f : Hom A X] [g : Hom B X] {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B),
      a .> f == b .> g -> Hom Γ (pullback f g);
  HasPullbacks_isPullback ::
    forall {A B X : Ob C} (f : Hom A X) (g : Hom B X),
      isPullback C f g (pullback f g) (@pullL _ _ _ f g) (@pullR _ _ _ f g) (@triple A B X f g);
}.

Arguments pullback [C _ A B X] _ _.
Arguments pullL    {C _ A B X f g}.
Arguments pullR    {C _ A B X f g}.
Arguments triple   [C _ A B X f g Γ] _ _ _.

Definition commutator
  {C : Cat} {hp : HasPullbacks C} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
  : Hom (pullback f g) (pullback g f)
  := triple pullR pullL (symmetry ok).

Lemma commutator_idem :
  forall {C : Cat} {hp : HasPullbacks C} {A B X : Ob C} (f : Hom A X) (g : Hom B X),
    commutator .> commutator == id (pullback f g).
Proof.
  unfold commutator; intros.
  apply equiv_pullback.
  - now rewrite comp_assoc, triple_pullL, triple_pullR, comp_id_l.
  - now rewrite comp_assoc, triple_pullR, triple_pullL, comp_id_l.
Qed.

Lemma isIso_commutator :
  forall {C : Cat} {hp : HasPullbacks C} {A B X : Ob C} (f : Hom A X) (g : Hom B X),
    isIso (commutator (f := f) (g := g)).
Proof.
  red; intros.
  exists commutator.
  now split; apply commutator_idem.
Qed.

Lemma pullback_comm :
  forall {C : Cat} {hp : HasPullbacks C} {A B X : Ob C} (f : Hom A X) (g : Hom B X),
    pullback f g ~ pullback g f.
Proof.
  red; intros.
  exists commutator.
  now now apply isIso_commutator.
Qed.

#[refine]
#[local]
Instance HasPullbacks_HasProducts_HasEqualizers
  {C : Cat} (hp : HasProducts C) (he : HasEqualizers C) : HasPullbacks C :=
{
  pullback := fun A B X f g => @equalizer _ _ (product A B) X (outl .> f) (outr .> g);
  pullL    := fun A B X f g => equalize (outl .> f) (outr .> g) .> outl;
  pullR    := fun A B X f g => equalize (outl .> f) (outr .> g) .> outr;
  triple   := fun A B X f g Γ a b Heq => factorize (fpair a b) _;
}.
Proof.
  - now rewrite <- !comp_assoc, fpair_outl, fpair_outr.
  - split; intros.
    + now rewrite !comp_assoc, Equalizer.ok.
    + now rewrite <- comp_assoc, factorize_equalize, fpair_outl.
    + now rewrite <- comp_assoc, factorize_equalize, fpair_outr.
    + now rewrite equiv_equalizer', equiv_product', !comp_assoc.
Defined.