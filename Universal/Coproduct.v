From Cat Require Export Cat.

Set Implicit Arguments.

Class isCoproduct
  (C : Cat) {A B : Ob C}
  (P : Ob C) (finl : Hom A P) (finr : Hom B P)
  (copair : forall {P' : Ob C}, Hom A P' -> Hom B P' -> Hom P P')
  : Prop :=
{
  finl_copair :
    forall (P' : Ob C) (f : Hom A P') (g : Hom B P'),
      finl .> copair f g == f;
  finr_copair :
    forall (P' : Ob C) (f : Hom A P') (g : Hom B P'),
      finr .> copair f g == g;
  copair_equiv :
    forall (P' : Ob C) (h1 h2 : Hom P P'),
      finl .> h1 == finl .> h2 -> finr .> h1 == finr .> h2 -> h1 == h2
}.

#[export] Hint Mode isCoproduct ! ! ! ! ! ! ! : core.
#[export] Hint Mode isCoproduct ! ! ! - - - - : core.

Class HasCoproducts (C : Cat) : Type :=
{
  coprodOb : forall (A B : Ob C), Ob C;
  finl : forall {A B : Ob C}, Hom A (coprodOb A B);
  finr : forall {A B : Ob C}, Hom B (coprodOb A B);
  copair :
    forall
      {A B P : Ob C} (f : Hom A P) (g : Hom B P), Hom (coprodOb A B) P;
  HasCoproducts_isCoproduct :>
    forall {A B : Ob C}, isCoproduct C (@coprodOb A B) finl finr (@copair A B);
}.

Arguments coprodOb {C HasCoproducts} _ _.
Arguments finl     {C HasCoproducts A B}.
Arguments finr     {C HasCoproducts A B}.
Arguments copair  {C HasCoproducts A B P} _ _.

Lemma copair_equiv' :
  forall
    {C : Cat} {A B : Ob C}
    {P : Ob C} {finl : Hom A P} {finr : Hom B P}
    {copair : forall {P' : Ob C} (finl' : Hom A P') (finr' : Hom B P'), Hom P P'}
    {isP : isCoproduct C P finl finr (@copair)}
    {Y : Ob C} (h1 h2 : Hom P Y),
      h1 == h2 <-> finl .> h1 == finl .> h2 /\ finr .> h1 == finr .> h2.
Proof.
  split.
  - now intros ->.
  - now intros []; apply copair_equiv.
Qed.

Section isCoproduct.

Context
  {C : Cat} {A B : Ob C}
  {P : Ob C} {finl : Hom A P} {finr : Hom B P}
  {copair : forall {P' : Ob C} (finl' : Hom A P') (finr' : Hom B P'), Hom P P'}
  {isP : isCoproduct C P finl finr (@copair)}
  [P' : Ob C] [f : Hom A P'] [g : Hom B P'].

Arguments copair {P'} _ _.

#[global] Instance Proper_copair :
  Proper (equiv ==> equiv ==> equiv) (@copair P').
Proof.
  intros h1 h1' Heq1 h2 h2' Heq2.
  now rewrite copair_equiv', !finl_copair, !finr_copair.
Defined.

Lemma copair_universal :
  forall h : Hom P P',
    copair f g == h <-> f == finl .> h /\ g == finr .> h.
Proof.
  now intros; rewrite copair_equiv', finl_copair, finr_copair.
Qed.

Lemma copair_unique :
  forall h : Hom P P',
    finl .> h == f -> finr .> h == g -> h == copair f g.
Proof.
  now intros; rewrite copair_equiv', finl_copair, finr_copair.
Qed.

Lemma copair_id :
  copair finl finr == id P.
Proof.
  now rewrite copair_equiv', finl_copair, finr_copair, !comp_id_r.
Qed.

Lemma copair_post :
  forall {Y : Ob C} {h : Hom P' Y},
    copair (f .> h) (g .> h) == copair f g .> h.
Proof.
  now intros; rewrite copair_equiv', <- !comp_assoc, !finl_copair, !finr_copair.
Qed.

End isCoproduct.

Lemma isCoproduct_uiso :
  forall
    (C : Cat) (A B : Ob C)
    (P1 : Ob C) (finl1 : Hom A P1) (finr1 : Hom B P1)
    (copair1 : forall (P1' : Ob C) (finl1' : Hom A P1') (finr1' : Hom B P1'), Hom P1 P1')
    (P2 : Ob C) (finl2 : Hom A P2) (finr2 : Hom B P2)
    (copair2 : forall (P2' : Ob C) (finl2' : Hom A P2') (finr2' : Hom B P2'), Hom P2 P2'),
      isCoproduct C P1 finl1 finr1 copair1 ->
      isCoproduct C P2 finl2 finr2 copair2 ->
        exists!! f : Hom P2 P1, isIso f /\ finl1 == finl2 .> f /\ finr1 == finr2 .> f.
Proof.
  intros * H1 H2.
  exists (copair2 P1 finl1 finr1).
  repeat split.
  - exists (copair1 P2 finl2 finr2).
    now rewrite !copair_equiv', <- !comp_assoc, !finl_copair, !finr_copair, !comp_id_r.
  - now rewrite finl_copair.
  - now rewrite finr_copair.
  - intros u (HIso & Heql & Heqr).
    now rewrite copair_equiv', finl_copair, finr_copair.
Qed.

Lemma isCoproduct_iso :
  forall
    (C : Cat) (A B : Ob C)
    (P1 : Ob C) (finl1 : Hom A P1) (finr1 : Hom B P1)
    (copair1 : forall (P1' : Ob C) (finl1' : Hom A P1') (finr1' : Hom B P1'), Hom P1 P1')
    (P2 : Ob C) (finl2 : Hom A P2) (finr2 : Hom B P2)
    (copair2 : forall (P2' : Ob C) (finl2' : Hom A P2') (finr2' : Hom B P2'), Hom P2 P2'),
      isCoproduct C P1 finl1 finr1 copair1 ->
      isCoproduct C P2 finl2 finr2 copair2 ->
        P1 ~ P2.
Proof.
  intros. destruct (isCoproduct_uiso H H0).
  symmetry. cat.
Qed.