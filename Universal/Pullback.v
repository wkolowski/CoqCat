From Cat Require Import Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct Equalizer.

Set Implicit Arguments.

Class isPullback
  (C : Cat) {A B X : Ob C} (f : Hom A X) (g : Hom B X)
  (P : Ob C) (pullL : Hom P A) (pullR : Hom P B)
  (factor : forall {P' : Ob C} (pullL' : Hom P' A) (pullR' : Hom P' B),
              pullL' .> f == pullR' .> g -> Hom P' P)
  : Prop :=
{
  isPullback_ok : pullL .> f == pullR .> g;
  factor_pullL :
    forall (P' : Ob C) (x : Hom P' A) (y : Hom P' B) (H : x .> f == y .> g),
      factor x y H .> pullL == x;
  factor_pullR :
    forall (P' : Ob C) (x : Hom P' A) (y : Hom P' B) (H : x .> f == y .> g),
      factor x y H .> pullR == y;
  equiv_pullback :
    forall (P' : Ob C) (h1 h2 : Hom P' P),
      h1 .> pullL == h2 .> pullL -> h1 .> pullR == h2 .> pullR -> h1 == h2;
}.

Lemma equiv_pullback' :
  forall
    {C : Cat} {A B X : Ob C} {f : Hom A X} {g : Hom B X}
    {P : Ob C} {pullL : Hom P A} {pullR : Hom P B}
    {factor : forall {P' : Ob C} (pullL' : Hom P' A) (pullR' : Hom P' B),
                  pullL' .> f == pullR' .> g -> Hom P' P}
    {isP : isPullback C f g P pullL pullR (@factor)}
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
  {factor : forall {P' : Ob C} (pullL' : Hom P' A) (pullR' : Hom P' B),
                pullL' .> f == pullR' .> g -> Hom P' P}
  {isP : isPullback C f g P pullL pullR (@factor)}
  [P' : Ob C] [x : Hom P' A] [y : Hom P' B] [H : x .> f == y .> g].

Arguments factor {P'} _ _.

(* #[global] Instance Proper_factor :
  Proper (equiv ==> equiv ==> equiv) (@factor X).
Proof.
  intros h1 h1' Heq1 h2 h2' Heq2.
  now rewrite equiv_pullback', !factor_pullL, !factor_pullR.
Defined. *)

Lemma factor_universal :
  forall h : Hom P' P,
    factor x y H == h <-> x == h .> pullL /\ y == h .> pullR.
Proof.
  now intros; rewrite equiv_pullback', factor_pullL, factor_pullR.
Qed.

Lemma factor_unique :
  forall h : Hom P' P,
    h .> pullL == x -> h .> pullR == y -> h == factor x y H.
Proof.
  now intros; rewrite equiv_pullback', factor_pullL, factor_pullR.
Qed.

Lemma factor_id :
  factor pullL pullR isPullback_ok == id P.
Proof.
  now rewrite equiv_pullback', factor_pullL, factor_pullR, !comp_id_l.
Qed.

Lemma factor_pre :
  forall {Y : Ob C} {h : Hom Y P'},
    exists H' : (h .> x) .> f == (h .> y) .> g,
      factor (h .> x) (h .> y) H' == h .> factor x y H.
Proof.
  esplit. Unshelve. all: cycle 1.
  - now rewrite comp_assoc, H.
  - now rewrite equiv_pullback', factor_pullL, factor_pullR,
      !comp_assoc, factor_pullL, factor_pullR.
Qed.

End isPullback.

Class HasPullbacks (C : Cat) : Type :=
{
  pullback : forall {A B X : Ob C}, Hom A X -> Hom B X -> Ob C;
  pullL : forall {A B X : Ob C} (f : Hom A X) (g : Hom B X), Hom (pullback f g) A;
  pullR : forall {A B X : Ob C} (f : Hom A X) (g : Hom B X), Hom (pullback f g) B;
  factor :
    forall {A B X : Ob C} (f : Hom A X) (g : Hom B X) {P : Ob C} (pullL : Hom P A) (pullR : Hom P B),
      pullL .> f == pullR .> g -> Hom P (pullback f g);
  HasPullbacks_isPullback :>
    forall (A B X : Ob C) (f : Hom A X) (g : Hom B X),
      isPullback C f g (pullback f g) (pullL f g) (pullR f g) (@factor A B X f g);
  (* Proper_pullback :
    forall (A B X : Ob C) (f f' : Hom A X) (g g' : Hom B X),
      f == f' -> g == g' -> JMequiv (id (pullback f g)) (id (pullback f' g'));
  Proper_pullL :
    forall (A B X : Ob C) (f f' : Hom A X) (g g' : Hom B X),
      f == f' -> g == g' -> JMequiv (pullL f g) (pullL f' g');
  Proper_pullR :
    forall (A B X : Ob C) (f f' : Hom A X) (g g' : Hom B X),
      f == f' -> g == g' -> JMequiv (pullR f g) (pullR f' g'); *)
}.

Arguments pullback [C _ A B X] _ _.
Arguments pullL      [C _ A B X] _ _.
Arguments pullR      [C _ A B X] _ _.
Arguments factor     [C _ A B X f g P pullL pullR] _.

Lemma isPullback_uiso :
  forall
    (C : Cat) (A B X : Ob C) (f : Hom A X) (g : Hom B X)
    (P1 : Ob C) (pullL1 : Hom P1 A) (pullR1 : Hom P1 B)
    (factor1 : forall (P1' : Ob C) (pullL1' : Hom P1' A) (pullR1' : Hom P1' B),
                 pullL1' .> f == pullR1' .> g -> Hom P1' P1)
    (P2 : Ob C) (pullL2 : Hom P2 A) (pullR2 : Hom P2 B)
    (factor2 : forall (P2' : Ob C) (pullL2' : Hom P2' A) (pullR2' : Hom P2' B),
                 pullL2' .> f == pullR2' .> g -> Hom P2' P2),
      isPullback C f g P1 pullL1 pullR1 factor1 ->
      isPullback C f g P2 pullL2 pullR2 factor2 ->
        exists!! f : Hom P1 P2, isIso f /\ f .> pullL2 == pullL1 /\ f .> pullR2 == pullR1.
Proof.
  intros * H1 H2.
  exists (factor2 _ pullL1 pullR1 isPullback_ok).
  repeat split.
  - exists (factor1 P2 pullL2 pullR2 isPullback_ok).
    now rewrite !equiv_pullback', !comp_assoc, !factor_pullL, !factor_pullR, !comp_id_l.
  - now rewrite factor_pullL.
  - now rewrite factor_pullR.
  - intros u (HIso & Heql & Heqr).
    now rewrite equiv_pullback', factor_pullL, factor_pullR.
Qed.

Lemma isPullback_iso :
  forall
    (C : Cat) (A B X : Ob C) (f : Hom A X) (g : Hom B X)
    (P1 : Ob C) (pullL1 : Hom P1 A) (pullR1 : Hom P1 B)
    (factor1 : forall (P1' : Ob C) (pullL1' : Hom P1' A) (pullR1' : Hom P1' B),
                 pullL1' .> f == pullR1' .> g -> Hom P1' P1)
    (P2 : Ob C) (pullL2 : Hom P2 A) (pullR2 : Hom P2 B)
    (factor2 : forall (P2' : Ob C) (pullL2' : Hom P2' A) (pullR2' : Hom P2' B),
                 pullL2' .> f == pullR2' .> g -> Hom P2' P2),
      isPullback C f g P1 pullL1 pullR1 factor1 ->
      isPullback C f g P2 pullL2 pullR2 factor2 ->
        P1 ~ P2.
Proof.
  intros. destruct (isPullback_uiso H H0).
  red. exists x. now destruct H1 as [[H1 _] _].
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
  - now apply (factor_pullL (isPullback := H)), equiv_terminal.
  - now apply (factor_pullR (isPullback := H)), equiv_terminal.
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
  (P : Ob C) (p : Hom P A) (factor : forall (P' : Ob C) (f : Hom P' A) (g : Hom P' A), Hom P' P) :
    isPullback C f g P p p (fun P' pullL' pullR' _ => factor P' pullL' pullR') ->
      isEqualizer C f g P p (fun (P' : Ob C) (p : Hom P' A) _ => factor P' p p).
Proof.
  split; intros.
  - apply isPullback_ok.
  - now apply (factor_pullL (isPullback := H)).
  - now apply equiv_pullback.
Qed.

(*
Lemma isEqualizer_isPullback'
  (C : Cat) (A B : Ob C) (f g : Hom A B)
  (P : Ob C) (p : Hom P A) (factor : forall (P' : Ob C) (f : Hom P' A) (g : Hom P' A), Hom P' P) :
    isPullback C f g P p p (fun P' pullL' pullR' _ => factor P' pullL' pullR') <->
      isEqualizer C f g P p (fun (P' : Ob C) (p : Hom P' A) _ => factor P' p p).
Proof.
  split; intros.
  - split; intros.
    + apply isPullback_ok.
    + now apply (factor_pullL (isPullback := H)).
    + now apply equiv_pullback.
  - split; intros.
    + apply equalize_ok.
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
        (* fpair (factorize E' e1 equalize_ok) (factorize E' e2 equalize_ok)). *)
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