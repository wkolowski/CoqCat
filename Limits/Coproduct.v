From Cat Require Export Cat.
From Cat.Limits Require Import Product.

Set Implicit Arguments.

Section Traditional.

Definition isCoproduct
  (C : Cat) {A B : Ob C}
  (P : Ob C) (finl : Hom A P) (finr : Hom B P)
  (copair : forall {X : Ob C} (f : Hom A X) (g : Hom B X), Hom P X)
  : Prop :=
    forall (X : Ob C) (f : Hom A X) (g : Hom B X),
      setoid_unique (fun d : Hom P X => f == finl .> d /\ g == finr .> d) (copair f g).

Lemma isProduct_Dual :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (finl : Hom X P) (finr : Hom Y P)
    (copair : forall (P' : Ob C) (f : Hom X P') (g : Hom Y P'), Hom P P'),
      isProduct (Dual C) P finl finr copair
        =
      isCoproduct C P finl finr copair.
Proof. reflexivity. Defined.

Lemma isCoproduct_Dual :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (outl : Hom P X) (outr : Hom P Y)
    (fpair : forall (P' : Ob C) (outl' : Hom P' X) (outr' : Hom P' Y), Hom P' P),
      isCoproduct (Dual C) P outl outr fpair
        =
      isProduct C P outl outr fpair.
Proof. reflexivity. Defined.

Lemma isCoproduct_uiso :
  forall
    (C : Cat) (X Y : Ob C)
    (P1 : Ob C) (finl1 : Hom X P1) (finr1 : Hom Y P1)
    (copair1 : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P1 A)
    (P2 : Ob C) (finl2 : Hom X P2) (finr2 : Hom Y P2)
    (copair2 : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P2 A),
      isCoproduct C P1 finl1 finr1 copair1 ->
      isCoproduct C P2 finl2 finr2 copair2 ->
        exists!! f : Hom P1 P2, isIso f /\ finl1 .> f == finl2 /\ finr1 .> f == finr2.
Proof.
  intros. do 2 red in H. do 2 red in H0.
  exists (copair1 _ finl2 finr2).
  red. repeat split.
    exists (copair2 _ finl1 finr1).
      destruct
        (H P1 finl1 finr1) as [[HP11 HP12] HP13],
        (H P2 finl2 finr2) as [[HP21 HP22] HP23],
        (H0 P1 finl1 finr1) as [[HP11' HP12'] HP13'],
        (H0 P2 finl2 finr2) as [[HP21' HP22'] HP23'].
      cat.
        rewrite <- (HP13 (copair1 P2 finl2 finr2 .> copair2 P1 finl1 finr1)).
          apply HP13. cat.
          cat; rewrite <- comp_assoc.
            rewrite <- HP21. assumption.
            rewrite <- HP22. assumption.
        rewrite <- (HP23' (copair2 P1 finl1 finr1 .> copair1 P2 finl2 finr2)).
          apply HP23'. cat.
          cat; rewrite <- comp_assoc.
            rewrite <- HP11'. assumption.
            rewrite <- HP12'. assumption.
    edestruct H as [[H1 H2] _]. rewrite <- H1. reflexivity.
    edestruct H as [[H1 H2] _]. rewrite <- H2. reflexivity.
    intros. destruct H1 as [[y_inv [iso1 iso2]] [eq1 eq2]].
      edestruct H. apply H2. split; [rewrite eq1 | rewrite eq2]; cat.
Qed.

Lemma isCoproduct_iso :
  forall
    (C : Cat) (X Y : Ob C)
    (P1 : Ob C) (finl1 : Hom X P1) (finr1 : Hom Y P1)
    (copair1 : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P1 A)
    (P2 : Ob C) (finl2 : Hom X P2) (finr2 : Hom Y P2)
    (copair2 : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P2 A),
      isCoproduct C P1 finl1 finr1 copair1 ->
      isCoproduct C P2 finl2 finr2 copair2 ->
        P1 ~ P2.
Proof.
  intros. destruct (isCoproduct_uiso H H0). cat.
Qed.

Lemma isCoproduct_copair_equiv :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (finl : Hom X P) (finr : Hom Y P)
    (copair1 copair2 : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      isCoproduct C P finl finr copair1 ->
      isCoproduct C P finl finr copair2 ->
        forall (A : Ob C) (f : Hom X A) (g : Hom Y A), copair1 A f g == copair2 A f g.
Proof.
  intros. edestruct H, H0. apply H2. cat.
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
  intros. do 2 red in H.
  destruct (H P finl1 finr) as [[H1 H2] H3].
  destruct (H0 P finl1 finr) as [[H1' H2'] H3'].
  rewrite (H3 (id P)) in H1'. cat. cat.
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
  intros. do 2 red in H.
  destruct (H P finl finr1) as [[H1 H2] H3].
  destruct (H0 P finl finr1) as [[H1' H2'] H3'].
  rewrite (H3 (id P)) in H2'. cat. cat.
Qed.

Lemma isCoproduct_comm :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (finl : Hom X P) (finr : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      isCoproduct C P finl finr copair ->
        isCoproduct C P finr finl (fun A f g => copair A g f).
Proof.
  unfold isCoproduct in *; intros.
  destruct (H X0 g f) as [[H1 H2] H3]. cat.
Qed.

End Traditional.

Class HasCoproducts (C : Cat) : Type :=
{
  coprodOb : Ob C -> Ob C -> Ob C;
  finl : forall A B : Ob C, Hom A (coprodOb A B);
  finr : forall A B : Ob C, Hom B (coprodOb A B);
  copair : forall {A B X : Ob C} (f : Hom A X) (g : Hom B X), Hom (coprodOb A B) X;
  Proper_copair :> forall (A B X : Ob C), Proper (equiv ==> equiv ==> equiv) (@copair A B X);
  is_coproduct :
    forall A B : Ob C, isCoproduct C (coprodOb A B) (finl A B) (finr A B) (@copair A B)
}.

Arguments coprodOb {C HasCoproducts} _ _.
Arguments finl  {C HasCoproducts A B}.
Arguments finr  {C HasCoproducts A B}.
Arguments copair   {C HasCoproducts A B X} _ _.

Lemma copair_finl :
  forall (C : Cat) (hp : HasCoproducts C) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
    finl .> copair f g == f.
Proof.
  intros. destruct hp; cbn. do 2 red in is_coproduct0.
  destruct (is_coproduct0 X Y A f g) as [[H1 H2] H3].
  rewrite <- H1. reflexivity.
Qed.

Lemma copair_finr :
  forall (C : Cat) (hp : HasCoproducts C) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
    finr .> copair f g == g.
Proof.
  intros. destruct hp; cbn. do 2 red in is_coproduct0.
  destruct (is_coproduct0 X Y A f g) as [[H1 H2] H3].
  rewrite <- H2. reflexivity.
Qed.

Lemma copair_post :
  forall
    (C : Cat) (hp : HasCoproducts C) (X Y A B : Ob C) (f1 : Hom X A) (f2 : Hom Y A) (g : Hom A B),
      copair f1 f2 .> g == copair (f1 .> g) (f2 .> g).
Proof.
  intros. destruct hp; cbn. do 2 red in is_coproduct0.
  destruct (is_coproduct0 X Y B (f1 .> g) (f2 .> g)) as [_ H3].
  destruct (is_coproduct0 X Y A f1 f2) as [[H1 H2] _].
  rewrite H3.
    reflexivity.
    split.
      rewrite <- comp_assoc, <- H1. reflexivity.
      rewrite <- comp_assoc, <- H2. reflexivity.
Qed.

Lemma copair_id :
  forall (C : Cat) (hp : HasCoproducts C) (X Y : Ob C),
    copair finl finr == id (coprodOb X Y).
Proof.
  destruct hp; cbn; intros. do 2 red in is_coproduct0.
  destruct (is_coproduct0 X Y (coprodOb0 X Y) (finl0 X Y) (finr0 X Y)) as [_ H3].
  apply H3. cat.
Qed.

Lemma copair_comp :
  forall
    (C : Cat) (hp : HasCoproducts C)
    (X Y X' Y' A : Ob C) (f : Hom X A) (g : Hom Y A) (h1 : Hom X' X) (h2 : Hom Y' Y),
      copair (h1 .> f) (h2 .> g) == copair (h1 .> finl) (h2 .> finr) .> copair f g.
Proof.
  intros. rewrite copair_post, !comp_assoc, copair_finl, copair_finr. reflexivity.
Qed.

Ltac copair := intros; try split;
repeat match goal with
| |- context [copair (finl .> ?x) (finr .> ?x)] => rewrite <- copair_post, copair_id
| |- context [copair _ _ .> _] => rewrite copair_post
| |- context [finl .> copair _ _] => rewrite copair_finl
| |- context [finr .> copair _ _] => rewrite copair_finr
| |- context [copair finl finr] => rewrite copair_id
| |- ?x == ?x => reflexivity
| |- copair _ _ == copair _ _ => apply Proper_copair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- copair _ _ == id (coprodOb _ _) => rewrite <- copair_id; apply Proper_copair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite ?comp_assoc; auto
end.

Lemma coprodOb_comm :
  forall (C : Cat) (hp : HasCoproducts C) (X Y : Ob C),
    coprodOb X Y ~ coprodOb Y X.
Proof.
  intros.
  red. exists (copair finr finl).
  red. exists (copair finr finl).
  copair.
Qed.

Lemma coprodOb_assoc :
  forall (C : Cat) (hp : HasCoproducts C) (X Y Z : Ob C),
    coprodOb X (coprodOb Y Z) ~ coprodOb (coprodOb X Y) Z.
Proof.
  intros.
  red. exists (copair (finl .> finl) (copair (finr .> finl) finr)).
  red. exists (copair (copair finl (finl .> finr)) (finr .> finr)).
  copair.
Qed.

Lemma coprodOb_assoc' :
  forall (C : Cat) (hp : HasCoproducts C) (X Y Z : Ob C),
    {f : Hom (coprodOb (coprodOb X Y) Z) (coprodOb X (coprodOb Y Z)) | isIso f}.
Proof.
  intros.
  exists (copair (copair finl (finl .> finr)) (finr .> finr)).
  red. exists (copair (finl .> finl) (copair (finr .> finl) finr)).
  copair.
Defined.

Definition CoproductFunctor_fmap
  {C : Cat} {hp : HasCoproducts C}
  {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
  : Hom (coprodOb X X') (coprodOb Y Y')
  := (copair (f .> finl) (g .> finr)).

#[export]
Instance Proper_CoproductFunctor_fmap :
  forall (C : Cat) (hp : HasCoproducts C) (X X' Y Y' : Ob C),
    Proper
      ((@equiv _ (HomSetoid X Y))  ==>
      (@equiv _ (HomSetoid X' Y'))  ==>
      (@equiv _ (HomSetoid (coprodOb X X') (coprodOb Y Y'))))
      (@CoproductFunctor_fmap C hp X X' Y Y').
Proof.
  unfold Proper, respectful, CoproductFunctor_fmap. copair.
Qed.

Lemma CoproductFunctor_fmap_id :
  forall (C : Cat) (hp : HasCoproducts C) (X Y : Ob C),
    CoproductFunctor_fmap (id X) (id Y) == id (coprodOb X Y).
Proof.
  intros; unfold CoproductFunctor_fmap. copair.
Defined.

Lemma CoproductFunctor_fmap_comp :
  forall
    (C : Cat) (hp : HasCoproducts C) (A1 A2 B1 B2 C1 C2 : Ob C)
    (f1 : Hom A1 B1) (g1 : Hom B1 C1) (f2 : Hom A2 B2) (g2 : Hom B2 C2),
      CoproductFunctor_fmap (f1 .> g1) (f2 .> g2)
        ==
      CoproductFunctor_fmap f1 f2 .> CoproductFunctor_fmap g1 g2.
Proof.
  unfold CoproductFunctor_fmap; intros. copair.
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
Instance CoproductFunctor {C : Cat} (hp : HasCoproducts C) : Functor (CAT_prodOb C C) C :=
{
  fob := fun P : Ob (CAT_prodOb C C) => coprodOb (fst P) (snd P);
  fmap := fun (X Y : Ob (CAT_prodOb C C)) (f : Hom X Y) => CoproductFunctor_fmap (fst f) (snd f)
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
  biob := @coprodOb C hp;
  bimap :=
    fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') => copair (f .> finl) (g .> finr)
}.
Proof.
  unfold Proper, respectful. all: copair.
Defined.

#[export]
Instance HasCoproducts_Dual (C : Cat) (hp : HasProducts C) : HasCoproducts (Dual C) :=
{
  coprodOb := @prodOb C hp;
  finl := @outl C hp;
  finr := @outr C hp;
  copair := @fpair C hp;
  Proper_copair := @Proper_fpair C hp;
  is_coproduct := @is_product C hp
}.

#[export]
Instance HasProducts_Dual (C : Cat) (hp : HasCoproducts C) : HasProducts (Dual C) :=
{
  prodOb := @coprodOb C hp;
  outl := @finl C hp;
  outr := @finr C hp;
  fpair := @copair C hp;
  Proper_fpair := @Proper_copair C hp;
  is_product := @is_coproduct C hp
}.

Module Universal.

Class HasCoproducts (C : Cat) : Type :=
{
  coprodOb : Ob C -> Ob C -> Ob C;
  finl : forall {A B : Ob C}, Hom A (coprodOb A B);
  finr : forall {A B : Ob C}, Hom B (coprodOb A B);
  copair :
    forall {A B X : Ob C} (f : Hom A X) (g : Hom B X), Hom (coprodOb A B) X;
  Proper_copair :>
    forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@copair A B X);
  copair_universal :
    forall {A B X : Ob C} (f : Hom A X) (g : Hom B X) (h : Hom (coprodOb A B) X),
      copair f g == h <-> f == finl .> h /\ g == finr .> h
}.

Arguments coprodOb {C HasCoproducts} _ _.
Arguments finl     {C HasCoproducts A B}.
Arguments finr     {C HasCoproducts A B}.
Arguments copair   {C HasCoproducts A B X} _ _.

Section HasCoproducts.

Context
  [C : Cat] [hp : HasCoproducts C]
  [A B X Y : Ob C]
  (f : Hom A X) (g : Hom B X).

Lemma copair_id :
  copair finl finr == id (coprodOb X Y).
Proof.
  rewrite copair_universal.
  cat.
Qed.

Lemma copair_finl :
  finl .> copair f g == f.
Proof.
  destruct (copair_universal f g (copair f g)) as [[<- _] _]; reflexivity.
Qed.

Lemma copair_finr :
  finr .> copair f g == g.
Proof.
  destruct (copair_universal f g (copair f g)) as [[_ <-] _]; reflexivity.
Qed.

Lemma copair_post :
  forall h : Hom X Y,
    copair (f .> h) (g .> h) == copair f g .> h.
Proof.
  intros h.
  rewrite copair_universal, <- !comp_assoc, copair_finl, copair_finr.
  split; reflexivity.
Qed.

End HasCoproducts.

Ltac coprod := intros; try split;
repeat match goal with
| |- context [copair (finl .> ?x) (finr .> ?x)] => rewrite copair_post, copair_id
| |- context [copair _ _ .> _] => rewrite <- copair_post
| |- context [finl .> copair _ _] => rewrite copair_finl
| |- context [finr .> copair _ _] => rewrite copair_finr
| |- context [copair finl finr] => rewrite copair_id
| |- ?x == ?x => reflexivity
| |- copair _ _ == copair _ _ => apply Proper_copair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- copair _ _ == id (coprodOb _ _) => rewrite <- copair_id; apply Proper_copair
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

End Universal.

Module Rules2.

Class HasCoproducts (C : Cat) : Type :=
{
  coprodOb : Ob C -> Ob C -> Ob C;
  finl : forall {A B : Ob C}, Hom A (coprodOb A B);
  finr : forall {A B : Ob C}, Hom B (coprodOb A B);
  copair :
    forall {A B X : Ob C} (f : Hom A X) (g : Hom B X), Hom (coprodOb A B) X;
  Proper_copair :>
    forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@copair A B X);
(* reflection *)
  copair_id :
    forall X Y : Ob C,
      copair finl finr == id (coprodOb X Y);
(* cancellation *)
  copair_finl :
    forall (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
      finl .> copair f g == f;
  copair_finr :
    forall (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
      finr .> copair f g == g;
(* fusion *)
  copair_post :
    forall (X Y A B : Ob C) (f1 : Hom X A) (f2 : Hom Y A) (g : Hom A B),
      copair (f1 .> g) (f2 .> g) == copair f1 f2 .> g
}.

Arguments coprodOb {C HasCoproducts} _ _.
Arguments finl     {C HasCoproducts A B}.
Arguments finr     {C HasCoproducts A B}.
Arguments copair   {C HasCoproducts A B X} _ _.

Ltac coprod := intros; try split;
repeat match goal with
| |- context [copair (finl .> ?x) (finr .> ?x)] => rewrite copair_post, copair_id
| |- context [copair _ _ .> _] => rewrite <- copair_post
| |- context [finl .> copair _ _] => rewrite copair_finl
| |- context [finr .> copair _ _] => rewrite copair_finr
| |- context [copair finl finr] => rewrite copair_id
| |- ?x == ?x => reflexivity
| |- copair _ _ == copair _ _ => apply Proper_copair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- copair _ _ == id (coprodOb _ _) => rewrite <- copair_id; apply Proper_copair
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

End Rules2.