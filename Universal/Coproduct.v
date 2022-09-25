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
  equiv_coproduct :
    forall (P' : Ob C) (h1 h2 : Hom P P'),
      finl .> h1 == finl .> h2 -> finr .> h1 == finr .> h2 -> h1 == h2
}.

#[export] Hint Mode isCoproduct ! ! ! ! ! ! ! : core.
#[export] Hint Mode isCoproduct ! ! ! - - - - : core.

Lemma equiv_coproduct' :
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
  - now intros []; apply equiv_coproduct.
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
  now rewrite equiv_coproduct', !finl_copair, !finr_copair.
Defined.

Lemma copair_universal :
  forall h : Hom P P',
    copair f g == h <-> f == finl .> h /\ g == finr .> h.
Proof.
  now intros; rewrite equiv_coproduct', finl_copair, finr_copair.
Qed.

Lemma copair_unique :
  forall h : Hom P P',
    finl .> h == f -> finr .> h == g -> h == copair f g.
Proof.
  now intros; rewrite equiv_coproduct', finl_copair, finr_copair.
Qed.

Lemma copair_id :
  copair finl finr == id P.
Proof.
  now rewrite equiv_coproduct', finl_copair, finr_copair, !comp_id_r.
Qed.

Lemma copair_comp :
  forall {Y : Ob C} {h : Hom P' Y},
    copair f g .> h == copair (f .> h) (g .> h).
Proof.
  now intros; rewrite equiv_coproduct', <- !comp_assoc, !finl_copair, !finr_copair.
Qed.

End isCoproduct.

Ltac coproduct_simpl :=
  repeat (rewrite
    ?equiv_coproduct', ?finl_copair, ?finr_copair, ?copair_id, ?copair_comp,
    ?comp_id_l, ?comp_id_r, ?comp_assoc).

Lemma isCoproduct_uiso :
  forall
    (C : Cat) (A B : Ob C)
    (P1 : Ob C) (finl1 : Hom A P1) (finr1 : Hom B P1)
    (copair1 : forall (P1' : Ob C) (finl1' : Hom A P1') (finr1' : Hom B P1'), Hom P1 P1')
    (P2 : Ob C) (finl2 : Hom A P2) (finr2 : Hom B P2)
    (copair2 : forall (P2' : Ob C) (finl2' : Hom A P2') (finr2' : Hom B P2'), Hom P2 P2'),
      isCoproduct C P1 finl1 finr1 copair1 ->
      isCoproduct C P2 finl2 finr2 copair2 ->
        exists!! f : Hom P1 P2, isIso f /\ finl2 == finl1 .> f /\ finr2 == finr1 .> f.
Proof.
  intros * H1 H2.
  exists (copair1 P2 finl2 finr2).
  repeat split.
  - exists (copair2 P1 finl1 finr1).
    now rewrite !equiv_coproduct', <- !comp_assoc, !finl_copair, !finr_copair, !comp_id_r.
  - now rewrite finl_copair.
  - now rewrite finr_copair.
  - intros u (HIso & Heql & Heqr).
    now rewrite equiv_coproduct', finl_copair, finr_copair.
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
  now intros; destruct (isCoproduct_uiso H H0) as [i []]; exists i.
Qed.

Lemma isCoproduct_equiv_copair :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (finl : Hom X P) (finr : Hom Y P)
    (copair1 copair2 : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      isCoproduct C P finl finr copair1 ->
      isCoproduct C P finl finr copair2 ->
        forall (A : Ob C) (f : Hom X A) (g : Hom Y A),
          copair1 A f g == copair2 A f g.
Proof.
  now intros; rewrite equiv_coproduct', !finl_copair, !finr_copair.
Qed.

Lemma isCoproduct_equiv_finl :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (finl1 finl2 : Hom X P) (finr : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      isCoproduct C P finl1 finr copair ->
      isCoproduct C P finl2 finr copair ->
        finl1 == finl2.
Proof.
  now intros; rewrite <- finl_copair, copair_id, comp_id_r.
Qed.

Lemma isCoproduct_equiv_finr :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (finl : Hom X P) (finr1 finr2 : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      isCoproduct C P finl finr1 copair ->
      isCoproduct C P finl finr2 copair ->
        finr1 == finr2.
Proof.
  now intros; rewrite <- finr_copair, copair_id, comp_id_r.
Qed.

Lemma iso_to_coproduct :
  forall
    (C : Cat) (A B : Ob C)
    (P : Ob C) (finl : Hom A P) (finr : Hom B P)
    (copair : forall P' : Ob C, Hom A P' -> Hom B P' -> Hom P P'),
      isCoproduct C P finl finr copair ->
        forall {P' : Ob C} (f : Hom P P') (H : isIso f),
          exists g : Hom P' P,
            isCoproduct C P' (finl .> f) (finr .> f) (fun Γ a b => g .> copair Γ a b).
Proof.
  intros * H P' f (g & Hfg & Hgf).
  exists g.
  split; intros.
  - now rewrite comp_assoc, <- (comp_assoc f g), Hfg, comp_id_l, finl_copair.
  - now rewrite comp_assoc, <- (comp_assoc f g), Hfg, comp_id_l, finr_copair.
  - rewrite <- (comp_id_l h1), <- (comp_id_l h2), <- Hgf, !comp_assoc; f_equiv.
    now rewrite equiv_coproduct', <- !comp_assoc.
Qed.

Lemma isCoproduct_comm :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (finl : Hom X P) (finr : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      isCoproduct C P finl finr copair ->
        isCoproduct C P finr finl (fun A f g => copair A g f).
Proof.
  split; intros.
  - now rewrite finr_copair.
  - now rewrite finl_copair.
  - now rewrite equiv_coproduct'.
Qed.

Class HasCoproducts (C : Cat) : Type :=
{
  coproduct : Ob C -> Ob C -> Ob C;
  finl      : forall {A B : Ob C}, Hom A (coproduct A B);
  finr      : forall {A B : Ob C}, Hom B (coproduct A B);
  copair    : forall {A B : Ob C} {P : Ob C} (f : Hom A P) (g : Hom B P), Hom (coproduct A B) P;
  isCoproduct_HasCoproducts' :>
    forall {A B : Ob C}, isCoproduct C (@coproduct A B) finl finr (@copair A B);
}.

Arguments coproduct {C HasCoproducts} _ _.
Arguments finl      {C HasCoproducts A B}.
Arguments finr      {C HasCoproducts A B}.
Arguments copair    {C HasCoproducts A B P} _ _.

Ltac solve_coproduct := intros; try split;
repeat match goal with
| |- context [copair (finl .> ?x) (finr .> ?x)] => rewrite <- copair_comp, copair_id
| |- context [copair _ _ .> _] => rewrite copair_comp
| |- context [finl .> copair _ _] => rewrite finl_copair
| |- context [finr .> copair _ _] => rewrite finr_copair
| |- context [copair finl finr] => rewrite copair_id
| |- ?x == ?x => reflexivity
| |- copair _ _ == _ => apply equiv_coproduct
| |- _ == copair _ _ => apply equiv_coproduct
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- copair _ _ == id (coproduct _ _) => rewrite <- copair_id; apply Proper_copair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite ?comp_assoc; auto
end.

Ltac coproduct_simpl' :=
repeat match goal with
| |- context [copair (finl .> ?x) (finr .> ?x)] => rewrite <- copair_comp, copair_id
| |- context [copair _ _ .> _] => rewrite copair_comp
| |- context [finl .> copair _ _] => rewrite finl_copair
| |- context [finr .> copair _ _] => rewrite finr_copair
| |- context [copair finl finr] => rewrite copair_id
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| H : context [copair (finl .> ?x) (finr .> ?x)] |- _ => rewrite <- copair_comp, copair_id in H
| H : context [copair _ _ .> _] |- _ => rewrite copair_comp in H
| H : context [finl .> copair _ _] |- _ => rewrite finl_copair in H
| H : context [finr .> copair _ _] |- _ => rewrite finr_copair in H
| H : context [copair finl finr] |- _ => rewrite copair_id in H
| H : context [id _ .> _] |- _ => rewrite comp_id_l in H
| H : context [_ .> id _] |- _ => rewrite comp_id_r in H
end.

Lemma copair_comp' :
  forall
    (C : Cat) (hp : HasCoproducts C) (X Y X' Y' A : Ob C)
    (f : Hom X A) (g : Hom Y A) (h1 : Hom X' X) (h2 : Hom Y' Y),
      copair (h1 .> finl) (h2 .> finr) .> copair f g == copair (h1 .> f) (h2 .> g).
Proof. now solve_coproduct. Qed.

Lemma copair_comp_id :
  forall (C : Cat) (hp : HasCoproducts C) (A X Y : Ob C) (f : Hom (coproduct X Y) A),
    copair (finl .> f) (finr .> f) == f.
Proof.
  now intros; rewrite equiv_coproduct', finl_copair, finr_copair.
Qed.

Definition commutator
  {C : Cat} {hp : HasCoproducts C} {A B : Ob C}
  : Hom (coproduct A B) (coproduct B A) :=
    copair finr finl.

Lemma commutator_idem :
  forall {C : Cat} {hp : HasCoproducts C} {A B : Ob C},
    commutator .> commutator == id (coproduct A B).
Proof.
  now unfold commutator; solve_coproduct.
Qed.

Lemma isIso_commutator :
  forall {C : Cat} {hp : HasCoproducts C} {A B : Ob C},
    isIso (@commutator _ _ A B).
Proof.
  red; intros.
  exists commutator.
  now split; apply commutator_idem.
Qed.

Lemma coproduct_comm :
  forall (C : Cat) (hp : HasCoproducts C) (X Y : Ob C),
    coproduct X Y ~ coproduct Y X.
Proof.
  red; intros.
  exists commutator.
  now apply isIso_commutator.
Qed.

Definition associator
  {C : Cat} {hp : HasCoproducts C} {A B C : Ob C}
  : Hom (coproduct (coproduct A B) C) (coproduct A (coproduct B C)) :=
    copair (copair finl (finl .> finr)) (finr .> finr).

Definition unassociator
  {C : Cat} {hp : HasCoproducts C} {A B C : Ob C}
  : Hom (coproduct A (coproduct B C)) (coproduct (coproduct A B) C) :=
    copair (finl .> finl) (copair (finr .> finl) finr).

Lemma associator_unassociator :
  forall {C : Cat} {hp : HasCoproducts C} {A B C : Ob C},
    associator .> unassociator == id (coproduct (coproduct A B) C).
Proof.
  now unfold associator, unassociator; solve_coproduct.
Qed.

Lemma unassociator_associator :
  forall {C : Cat} {hp : HasCoproducts C} {A B C : Ob C},
    unassociator .> associator == id (coproduct A (coproduct B C)).
Proof.
  now unfold associator, unassociator; solve_coproduct.
Qed.

Lemma isIso_associator :
  forall {C : Cat} {hp : HasCoproducts C} {A B C : Ob C},
    isIso (@associator _ _ A B C).
Proof.
  red; intros.
  exists unassociator.
  split.
  - now apply associator_unassociator.
  - now apply unassociator_associator.
Qed.

Lemma isIso_unassociator :
  forall {C : Cat} {hp : HasCoproducts C} {A B C : Ob C},
    isIso (@unassociator _ _ A B C).
Proof.
  red; intros.
  exists associator.
  split.
  - now apply unassociator_associator.
  - now apply associator_unassociator.
Qed.

Lemma coproduct_assoc :
  forall (C : Cat) (hp : HasCoproducts C) (X Y Z : Ob C),
    coproduct X (coproduct Y Z) ~ coproduct (coproduct X Y) Z.
Proof.
  red; intros.
  exists unassociator.
  now apply isIso_unassociator.
Qed.

Lemma coproduct_assoc' :
  forall (C : Cat) (hp : HasCoproducts C) (X Y Z : Ob C),
    {f : Hom (coproduct (coproduct X Y) Z) (coproduct X (coproduct Y Z)) | isIso f}.
Proof.
  intros.
  exists associator.
  now apply isIso_associator.
Defined.

#[refine]
#[export]
Instance CoproductBifunctor {C : Cat} {hp : HasCoproducts C} : Bifunctor C C C :=
{
  biob := @coproduct C hp;
  bimap := fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') => copair (f .> finl) (g .> finr)
}.
Proof.
  - now proper.
  - now solve_coproduct.
  - now solve_coproduct.
Defined.

Notation "A + B" := (@biob _ _ _ (@CoproductBifunctor _ _) A B).
Notation "f +' g" := (@bimap _ _ _ (@CoproductBifunctor _ _) _ _ _ _ f g) (at level 40).