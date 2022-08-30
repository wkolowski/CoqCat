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

Lemma isCoproduct_copair_equiv :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (finl : Hom X P) (finr : Hom Y P)
    (copair1 copair2 : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      isCoproduct C P finl finr copair1 ->
      isCoproduct C P finl finr copair2 ->
        forall (A : Ob C) (f : Hom X A) (g : Hom Y A),
          copair1 A f g == copair2 A f g.
Proof.
  now intros; rewrite copair_equiv', !finl_copair, !finr_copair.
Qed.

Lemma isCoproduct_finl_equiv :
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

Lemma isCoproduct_finr_equiv :
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

Lemma iso_to_coprod :
  forall
    (C : Cat) (A B : Ob C)
    (P : Ob C) (finl : Hom A P) (finr : Hom B P)
    (copair : forall P' : Ob C, Hom A P' -> Hom B P' -> Hom P P'),
      isCoproduct C P finl finr copair ->
        forall {P' : Ob C} (f : Hom P P') (H : isIso f),
          isCoproduct C P' (finl .> f) (finr .> f)
            (fun (P'' : Ob C) (finl' : Hom A P'') (finr' : Hom B P'') =>
              match constructive_indefinite_description _ H with
              | exist _ g _ => g .> copair P'' finl' finr'
              end).
Proof.
  intros.
  destruct (constructive_indefinite_description _ _) as (f_inv & Heq1 & Heq2).
  split; intros.
  - now rewrite comp_assoc, <- (comp_assoc f f_inv), Heq1, comp_id_l, finl_copair.
  - now rewrite comp_assoc, <- (comp_assoc f f_inv), Heq1, comp_id_l, finr_copair.
  - rewrite <- (comp_id_l _ _ h1), <- (comp_id_l _ _ h2), <- Heq2, !comp_assoc; f_equiv.
    now rewrite copair_equiv', <- !comp_assoc.
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
  - now rewrite copair_equiv'.
Qed.

(* Class HasCoproducts' (C : Cat) (coproduct : Ob C -> Ob C -> Ob C) : Type :=
{
  finl     : forall {A B : Ob C}, Hom A (coproduct A B);
  finr     : forall {A B : Ob C}, Hom B (coproduct A B);
  copair   : forall {A B : Ob C} {P : Ob C} (f : Hom A P) (g : Hom B P), Hom (coproduct A B) P;
  isCoproduct_HasCoproducts' :>
    forall {A B : Ob C}, isCoproduct C (@coproduct A B) finl finr (@copair A B);
}.

Arguments finl     {C coproduct HasCoproducts' A B}.
Arguments finr     {C coproduct HasCoproducts' A B}.
Arguments copair   {C coproduct HasCoproducts' A B P} _ _.

Class HasCoproducts (C : Cat) : Type :=
{
  coproduct : forall (A B : Ob C), Ob C;
  HasCoproducts'_HasCoproducts :> HasCoproducts' C coproduct;
}.

Arguments coproduct {C HasCoproducts} _ _.

Coercion HasCoproducts'_HasCoproducts : HasCoproducts >-> HasCoproducts'. *)

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

Arguments coproduct {C HasCoproducts} _ _.

Ltac coprod := intros; try split;
repeat match goal with
| |- context [copair (finl .> ?x) (finr .> ?x)] => rewrite copair_post, copair_id
| |- context [copair _ _ .> _] => rewrite <- copair_post
| |- context [finl .> copair _ _] => rewrite finl_copair
| |- context [finr .> copair _ _] => rewrite finr_copair
| |- context [copair finl finr] => rewrite copair_id
| |- ?x == ?x => reflexivity
| |- copair _ _ == copair _ _ => apply Proper_copair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- copair _ _ == id (coproduct _ _) => rewrite <- copair_id; apply Proper_copair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite ?comp_assoc; auto
end.

Lemma copair_comp :
  forall
    (C : Cat) (hp : HasCoproducts C) (X Y X' Y' A : Ob C)
    (f : Hom X A) (g : Hom Y A) (h1 : Hom X' X) (h2 : Hom Y' Y),
      copair (h1 .> f) (h2 .> g) == copair (h1 .> finl) (h2 .> finr) .> copair f g.
Proof. coprod. Qed.

Lemma copair_post_id :
  forall (C : Cat) (hp : HasCoproducts C) (A X Y : Ob C) (f : Hom (coproduct X Y) A),
    copair (finl .> f) (finr .> f) == f.
Proof.
  now intros; rewrite copair_equiv', finl_copair, finr_copair.
Qed.

Lemma coproduct_comm :
  forall (C : Cat) (hp : HasCoproducts C) (X Y : Ob C),
    coproduct X Y ~ coproduct Y X.
Proof.
  intros.
  red. exists (copair finr finl).
  red. exists (copair finr finl).
  coprod.
Qed.

Lemma coproduct_assoc :
  forall (C : Cat) (hp : HasCoproducts C) (X Y Z : Ob C),
    coproduct X (coproduct Y Z) ~ coproduct (coproduct X Y) Z.
Proof.
  intros.
  red. exists (copair (finl .> finl) (copair (finr .> finl) finr)).
  red. exists (copair (copair finl (finl .> finr)) (finr .> finr)).
  coprod.
Qed.

Lemma coproduct_assoc' :
  forall (C : Cat) (hp : HasCoproducts C) (X Y Z : Ob C),
    {f : Hom (coproduct (coproduct X Y) Z) (coproduct X (coproduct Y Z)) | isIso f}.
Proof.
  intros.
  exists (copair (copair finl (finl .> finr)) (finr .> finr)).
  exists (copair (finl .> finl) (copair (finr .> finl) finr)).
  coprod.
Defined.

Definition CoproductFunctor_fmap
  {C : Cat} {hp : HasCoproducts C}
  {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
  : Hom (coproduct X X') (coproduct Y Y')
  := (copair (f .> finl) (g .> finr)).

#[export]
Instance Proper_CoproductFunctor_fmap :
  forall (C : Cat) (hp : HasCoproducts C) (X X' Y Y' : Ob C),
    Proper
      ((@equiv _ (HomSetoid X Y))  ==>
      (@equiv _ (HomSetoid X' Y'))  ==>
      (@equiv _ (HomSetoid (coproduct X X') (coproduct Y Y'))))
      (@CoproductFunctor_fmap C hp X X' Y Y').
Proof.
  unfold Proper, respectful, CoproductFunctor_fmap. coprod.
Qed.

Lemma CoproductFunctor_fmap_id :
  forall (C : Cat) (hp : HasCoproducts C) (X Y : Ob C),
    CoproductFunctor_fmap (id X) (id Y) == id (coproduct X Y).
Proof.
  intros; unfold CoproductFunctor_fmap. coprod.
Defined.

Lemma CoproductFunctor_fmap_comp :
  forall
    (C : Cat) (hp : HasCoproducts C) (A1 A2 B1 B2 C1 C2 : Ob C)
    (f1 : Hom A1 B1) (g1 : Hom B1 C1) (f2 : Hom A2 B2) (g2 : Hom B2 C2),
      CoproductFunctor_fmap (f1 .> g1) (f2 .> g2)
        ==
      CoproductFunctor_fmap f1 f2 .> CoproductFunctor_fmap g1 g2.
Proof.
  unfold CoproductFunctor_fmap; intros. coprod.
Defined.

Lemma CoproductFunctor_fmap_comp_l :
  forall
    {C : Cat} {hp : HasCoproducts C}
    {X Y : Ob C} (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
      CoproductFunctor_fmap (f .> g) (id Z)
        ==
      CoproductFunctor_fmap f (id Z) .> CoproductFunctor_fmap g (id Z).
Proof.
  intros. rewrite <- CoproductFunctor_fmap_comp. cat.
Defined.

Lemma CoproductFunctor_fmap_comp_r :
  forall
    {C : Cat} {hp : HasCoproducts C}
    {X Y : Ob C} (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
      CoproductFunctor_fmap (id Z) (f .> g)
        ==
      CoproductFunctor_fmap (id Z) f .> CoproductFunctor_fmap (id Z) g.
Proof.
  intros. rewrite <- CoproductFunctor_fmap_comp. cat.
Defined.

#[refine]
#[export]
Instance CoproductFunctor {C : Cat} (hp : HasCoproducts C) : Functor (CAT_product C C) C :=
{
  fob := fun P : Ob (CAT_product C C) => coproduct (fst P) (snd P);
  fmap := fun (X Y : Ob (CAT_product C C)) (f : Hom X Y) => CoproductFunctor_fmap (fst f) (snd f)
}.
Proof.
  proper. apply Proper_CoproductFunctor_fmap; cat.
  intros. apply CoproductFunctor_fmap_comp.
  intros. apply CoproductFunctor_fmap_id.
Defined.

Notation "A + B" := (fob CoproductFunctor (A, B)).
Notation "f +' g" := (CoproductFunctor_fmap f g) (at level 40).

#[refine]
#[export]
Instance CoproductBifunctor {C : Cat} {hp : HasCoproducts C} : Bifunctor C C C :=
{
  biob := @coproduct C hp;
  bimap :=
    fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') => copair (f .> finl) (g .> finr)
}.
Proof.
  unfold Proper, respectful. all: coprod.
Defined.