From Cat Require Import Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct Equalizer.

Set Implicit Arguments.

Class isPullback
  (C : Cat) {A B X : Ob C} (f : Hom A X) (g : Hom B X)
  (P : Ob C) (pullL : Hom P A) (pullR : Hom P B)
  (triple : forall {P' : Ob C} (pullL' : Hom P' A) (pullR' : Hom P' B),
              pullL' .> f == pullR' .> g -> Hom P' P)
  : Prop :=
{
  pullback_ok : pullL .> f == pullR .> g;
  triple_pullL :
    forall (P' : Ob C) (x : Hom P' A) (y : Hom P' B) (H : x .> f == y .> g),
      triple x y H .> pullL == x;
  triple_pullR :
    forall (P' : Ob C) (x : Hom P' A) (y : Hom P' B) (H : x .> f == y .> g),
      triple x y H .> pullR == y;
  equiv_pullback :
    forall (P' : Ob C) (h1 h2 : Hom P' P),
      h1 .> pullL == h2 .> pullL -> h1 .> pullR == h2 .> pullR -> h1 == h2;
}.

#[export] Hint Mode isPullback ! ! ! ! ! ! ! ! ! ! : core.
#[export] Hint Mode isPullback ! ! ! ! ! - - - - - : core.

Lemma equiv_pullback' :
  forall
    {C : Cat} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
    {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
    {triple : forall {P' : Ob C} (pullL' : Hom P' A) (pullR' : Hom P' B),
                  pullL' .> f == pullR' .> g -> Hom P' P}
    {isP : isPullback C f g P pullL pullR (@triple)}
    {P' : Ob C} (h1 h2 : Hom P' P),
      h1 == h2 <-> h1 .> pullL == h2 .> pullL /\ h1 .> pullR == h2 .> pullR.
Proof.
  split.
  - now intros ->.
  - now intros []; apply equiv_pullback.
Qed.

Section isPullback.

Context
  {C : Cat} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
  {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
  {triple : forall {P' : Ob C} (pullL' : Hom P' A) (pullR' : Hom P' B),
                pullL' .> f == pullR' .> g -> Hom P' P}
  {isP : isPullback C f g P pullL pullR (@triple)}
  [P' : Ob C] [x : Hom P' A] [y : Hom P' B] [H : x .> f == y .> g].

Arguments triple {P'} _ _.

(* #[global] Instance Proper_triple :
  Proper (equiv ==> equiv ==> equiv) (@triple X).
Proof.
  intros h1 h1' Heq1 h2 h2' Heq2.
  now rewrite equiv_pullback', !triple_pullL, !triple_pullR.
Defined. *)

Lemma triple_universal :
  forall h : Hom P' P,
    triple x y H == h <-> x == h .> pullL /\ y == h .> pullR.
Proof.
  now intros; rewrite equiv_pullback', triple_pullL, triple_pullR.
Qed.

Lemma triple_unique :
  forall h : Hom P' P,
    h .> pullL == x -> h .> pullR == y -> h == triple x y H.
Proof.
  now intros; rewrite equiv_pullback', triple_pullL, triple_pullR.
Qed.

Lemma triple_id :
  triple pullL pullR pullback_ok == id P.
Proof.
  now rewrite equiv_pullback', triple_pullL, triple_pullR, !comp_id_l.
Qed.

Lemma triple_pre :
  forall {Y : Ob C} {h : Hom Y P'},
    exists H' : (h .> x) .> f == (h .> y) .> g,
      triple (h .> x) (h .> y) H' == h .> triple x y H.
Proof.
  esplit. Unshelve. all: cycle 1.
  - now rewrite comp_assoc, H.
  - now rewrite equiv_pullback', triple_pullL, triple_pullR,
      !comp_assoc, triple_pullL, triple_pullR.
Qed.

End isPullback.

Ltac pullback_simpl :=
  repeat (rewrite
    ?equiv_pullback', ?triple_pullL, ?triple_pullR, ?triple_id,
    ?comp_id_l, ?comp_id_r, ?comp_assoc).

Lemma isPullback_uiso :
  forall
    (C : Cat) (A B X : Ob C) (f : Hom A X) (g : Hom B X)
    (P1 : Ob C) (pullL1 : Hom P1 A) (pullR1 : Hom P1 B)
    (triple1 : forall (P1' : Ob C) (pullL1' : Hom P1' A) (pullR1' : Hom P1' B),
                 pullL1' .> f == pullR1' .> g -> Hom P1' P1)
    (P2 : Ob C) (pullL2 : Hom P2 A) (pullR2 : Hom P2 B)
    (triple2 : forall (P2' : Ob C) (pullL2' : Hom P2' A) (pullR2' : Hom P2' B),
                 pullL2' .> f == pullR2' .> g -> Hom P2' P2),
      isPullback C f g P1 pullL1 pullR1 triple1 ->
      isPullback C f g P2 pullL2 pullR2 triple2 ->
        exists!! f : Hom P1 P2, isIso f /\ f .> pullL2 == pullL1 /\ f .> pullR2 == pullR1.
Proof.
  intros * H1 H2.
  exists (triple2 _ pullL1 pullR1 pullback_ok).
  repeat split.
  - exists (triple1 P2 pullL2 pullR2 pullback_ok).
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
    (triple1 : forall (P1' : Ob C) (pullL1' : Hom P1' A) (pullR1' : Hom P1' B),
                 pullL1' .> f == pullR1' .> g -> Hom P1' P1)
    (P2 : Ob C) (pullL2 : Hom P2 A) (pullR2 : Hom P2 B)
    (triple2 : forall (P2' : Ob C) (pullL2' : Hom P2' A) (pullR2' : Hom P2' B),
                 pullL2' .> f == pullR2' .> g -> Hom P2' P2),
      isPullback C f g P1 pullL1 pullR1 triple1 ->
      isPullback C f g P2 pullL2 pullR2 triple2 ->
        P1 ~ P2.
Proof.
  intros. destruct (isPullback_uiso H H0).
  red. exists x. now destruct H1 as [[H1 _] _].
Qed.

Lemma isMono_pullL :
  forall
    {C : Cat} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
    {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
    {triple : forall {Γ : Ob C} (x : Hom Γ A) (y : Hom Γ B), x .> f == y .> g -> Hom Γ P},
      isPullback C f g P pullL pullR (@triple) ->
        isMono g -> isMono pullL.
Proof.
  unfold isMono; intros * HisP Hg Y h1 h2 Heq.
  apply equiv_pullback; [easy |].
  apply Hg.
  now rewrite !comp_assoc, <- pullback_ok, <- !comp_assoc, Heq.
Qed.

Lemma isMono_pullR :
  forall
    {C : Cat} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
    {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
    {triple : forall {Γ : Ob C} (x : Hom Γ A) (y : Hom Γ B), x .> f == y .> g -> Hom Γ P},
      isPullback C f g P pullL pullR (@triple) ->
        isMono f -> isMono pullR.
Proof.
  unfold isMono; intros * HisP Hf Y h1 h2 Heq.
  apply equiv_pullback; [| easy].
  apply Hf.
  now rewrite !comp_assoc, pullback_ok, <- !comp_assoc, Heq.
Qed.

Lemma isIso_pullL :
  forall
    {C : Cat} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
    {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
    {triple : forall {Γ : Ob C} (x : Hom Γ A) (y : Hom Γ B), x .> f == y .> g -> Hom Γ P},
      isPullback C f g P pullL pullR (@triple) ->
        isIso g -> isIso pullL.
Proof.
  unfold isIso; intros * HisP (g' & Heq1 & Heq2).
  esplit. Unshelve. all: cycle 1.
  - apply (triple A (id A) (f .> g')).
    abstract (now rewrite comp_assoc, Heq2, comp_id_l, comp_id_r).
  - pullback_simpl; repeat split; [easy | | easy].
    now rewrite <- comp_assoc, pullback_ok, comp_assoc, Heq1, comp_id_r.
Qed.

Lemma isIso_pullR :
  forall
    {C : Cat} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
    {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
    {triple : forall {Γ : Ob C} (x : Hom Γ A) (y : Hom Γ B), x .> f == y .> g -> Hom Γ P},
      isPullback C f g P pullL pullR (@triple) ->
        isIso f -> isIso pullR.
Proof.
  unfold isIso; intros * HisP (f' & Heq1 & Heq2).
  esplit. Unshelve. all: cycle 1.
  - apply (triple B (g .> f') (id B)).
    abstract (now rewrite comp_assoc, Heq2, comp_id_l, comp_id_r).
  - pullback_simpl; repeat split; [| easy | easy].
    now rewrite <- comp_assoc, <- pullback_ok, comp_assoc, Heq1, comp_id_r.
Qed.

Lemma isPullback_id_l :
  forall {C : Cat} {B X : Ob C} (g : Hom B X),
    isPullback C (id X) g B g (id B) (fun Γ x y H => y).
Proof.
  split; intros.
  - now rewrite comp_id_l, comp_id_r.
  - now rewrite <- H, comp_id_r.
  - now rewrite comp_id_r.
  - now rewrite !comp_id_r in H0.
Qed.

Lemma isPullback_id_r :
  forall {C : Cat} {A X : Ob C} (f : Hom A X),
    isPullback C f (id X) A (id A) f (fun Γ x y H => x).
Proof.
  split; intros.
  - now rewrite comp_id_l, comp_id_r.
  - now rewrite comp_id_r.
  - now rewrite H, comp_id_r.
  - now rewrite !comp_id_r in H.
Qed.

Lemma reassoc_l :
  forall {C : Cat} {X Y Z W : Ob C} {f : Hom X Y} {g : Hom Y Z} {h : Hom Z W} {r : Hom X W},
    f .> (g .> h) == r -> (f .> g) .> h == r.
Proof.
  now intros; rewrite comp_assoc.
Qed.

Lemma isPullback_comp :
  forall
    {C : Cat} {A A' B X : Ob C} {f : Hom A X} {g : Hom B X} {h : Hom A' A}
    {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
    {triple : forall {Γ : Ob C} (x : Hom Γ A) (y : Hom Γ B), x .> f == y .> g -> Hom Γ P}
    (HisP : isPullback C f g P pullL pullR (@triple))
    {Q : Ob C} {pullL' : Hom Q A'} {pullR' : Hom Q P}
    {triple' : forall {Γ : Ob C} (x : Hom Γ A') (y : Hom Γ P), x .> h == y .> pullL -> Hom Γ Q}
    (HisP' : isPullback C h pullL Q pullL' pullR' (@triple')),
      isPullback C (h .> f) g Q pullL' (pullR' .> pullR)
        (fun Γ x y H =>
          triple' x (triple (x .> h) y (reassoc_l H)) ltac:(now rewrite triple_pullL)).
Proof.
  split.
  - rewrite <- comp_assoc, pullback_ok, !comp_assoc; f_equiv.
    now apply pullback_ok.
  - now intros; rewrite triple_pullL.
  - now intros; rewrite <- comp_assoc, !triple_pullR.
  - intros * Heq1 Heq2.
    apply equiv_pullback; [easy |].
    apply equiv_pullback.
    + now rewrite !comp_assoc, <- pullback_ok, <- !comp_assoc, Heq1.
    + now rewrite !comp_assoc, Heq2.
Qed.

Lemma isProduct_isPullback :
  forall
    (C : Cat) (ht : HasTerm C) (A B : Ob C)
    (P : Ob C) (pullL : Hom P A) (pullR : Hom P B)
    (fpair : forall (P' : Ob C) (pullL' : Hom P' A) (pullR' : Hom P' B), Hom P' P),
      isPullback C (delete A) (delete B) P pullL pullR
        (fun (P' : Ob C) (pullL' : Hom P' A) (pullR' : Hom P' B)
             (H : pullL' .> delete A == pullR' .> delete B) => fpair P' pullL' pullR') ->
        isProduct C P pullL pullR fpair.
Proof.
  split; intros.
  - now apply (triple_pullL (isPullback := H)), equiv_terminal.
  - now apply (triple_pullR (isPullback := H)), equiv_terminal.
  - now apply equiv_pullback.
Qed.

Lemma isPullback_isProduct :
  forall
    (C : Cat) (ht : HasTerm C) (A B : Ob C)
    (P : Ob C) (pullL : Hom P A) (pullR : Hom P B)
    (fpair : forall (P' : Ob C) (f : Hom P' A) (g : Hom P' B), Hom P' P),
      isProduct C P pullL pullR fpair ->
        isPullback C
          (delete A) (delete B) P pullL pullR (fun (P' : Ob C)
          (pullL' : Hom P' A) (pullR' : Hom P' B) _ => fpair P' pullL' pullR').
Proof.
  split; intros.
  - apply equiv_terminal.
  - now rewrite fpair_outl.
  - now rewrite fpair_outr.
  - now apply equiv_product.
Qed.

Lemma isEqualizer_isPullback
  (C : Cat) (A B : Ob C) (f g : Hom A B)
  (P : Ob C) (p : Hom P A) (triple : forall (P' : Ob C) (f : Hom P' A) (g : Hom P' A), Hom P' P) :
    isPullback C f g P p p (fun P' pullL' pullR' _ => triple P' pullL' pullR') ->
      isEqualizer C f g P p (fun (P' : Ob C) (p : Hom P' A) _ => triple P' p p).
Proof.
  split; intros.
  - apply pullback_ok.
  - now apply (triple_pullL (isPullback := H)).
  - now apply equiv_pullback.
Qed.

(*
Lemma isEqualizer_isPullback'
  (C : Cat) (A B : Ob C) (f g : Hom A B)
  (P : Ob C) (p : Hom P A) (triple : forall (P' : Ob C) (f : Hom P' A) (g : Hom P' A), Hom P' P) :
    isPullback C f g P p p (fun P' pullL' pullR' _ => triple P' pullL' pullR') <->
      isEqualizer C f g P p (fun (P' : Ob C) (p : Hom P' A) _ => triple P' p p).
Proof.
  split; intros.
  - split; intros.
    + apply pullback_ok.
    + now apply (triple_pullL (isPullback := H)).
    + now apply equiv_pullback.
  - split; intros.
    + apply equalizer_ok.
    + pose (h' := factorize_equalize (e' := x) (isEqualizer := H)).
      cbn in h'.
Abort.

Lemma isPullback_isEqualizer :
  forall (C : Cat) (hp : HasProducts C) (A B : Ob C) (f g : Hom A B)
  (E : Ob C) (e e1 : Hom E A) (e2 : Hom E A)
  (factorize : forall (E' : Ob C) (e : Hom E' A), e .> f == e .> g -> Hom E' E),
    isEqualizer C f g E e factorize ->
(*     isEqualizer C f g E e2 factorize -> *)
    isPullback C f g (product E E) (outl .> e) (outr .> e)
      (fun (E' : Ob C) (e1 e2 : Hom E' A) (H : e1 .> f == e2 .> g) =>
        fpair e1 e2).
        (* fpair (factorize E' e1 equalizer_ok) (factorize E' e2 equalizer_ok)). *)
Proof.
  intros. pose (eq := isEqualizer_equiv H H0).
  repeat split.
    rewrite eq. edestruct H0. assocr'. rewrite e.
      f_equiv. destruct hp. cbn in *. do 2 red in is_product.
Abort.
*)

(* 
https://math.stackexchange.com/questions/308391/products-and-pullbacks-imply-equalizers

Zhen Lin *)

Class HasPullbacks (C : Cat) : Type :=
{
  pullback : forall {A B X : Ob C}, Hom A X -> Hom B X -> Ob C;
  pullL : forall {A B X : Ob C} {f : Hom A X} {g : Hom B X}, Hom (pullback f g) A;
  pullR : forall {A B X : Ob C} {f : Hom A X} {g : Hom B X}, Hom (pullback f g) B;
  triple :
    forall {A B X : Ob C} [f : Hom A X] [g : Hom B X] {P : Ob C} (pullL' : Hom P A) (pullR' : Hom P B),
      pullL' .> f == pullR' .> g -> Hom P (pullback f g);
  HasPullbacks_isPullback :>
    forall (A B X : Ob C) (f : Hom A X) (g : Hom B X),
      isPullback C f g (pullback f g) (@pullL _ _ _ f g) (@pullR _ _ _ f g) (@triple A B X f g);
}.

Arguments pullback [C _ A B X] _ _.
Arguments pullL    {C _ A B X f g}.
Arguments pullR    {C _ A B X f g}.
Arguments triple   [C _ A B X f g P] _ _ _.