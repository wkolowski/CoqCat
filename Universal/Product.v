From Cat Require Export Cat.

Set Implicit Arguments.

Class isProduct
  (C : Cat) {A B : Ob C}
  (P : Ob C) (outl : Hom P A) (outr : Hom P B)
  (fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P)
  : Prop :=
{
  fpair_outl :
    forall {X : Ob C} (f : Hom X A) (g : Hom X B),
      fpair f g .> outl == f;
  fpair_outr :
    forall {X : Ob C} (f : Hom X A) (g : Hom X B),
      fpair f g .> outr == g;
  fpair_equiv :
    forall {X : Ob C} (f g : Hom X P),
      f .> outl == g .> outl -> f .> outr == g .> outr -> f == g
}.

#[export] Hint Mode isProduct ! ! ! ! ! ! ! : core.
#[export] Hint Mode isProduct ! ! ! - - - - : core.

Lemma fpair_equiv' :
  forall
    {C : Cat} {A B : Ob C}
    {P : Ob C} {outl : Hom P A} {outr : Hom P B}
    {fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P}
    {isP : isProduct C P outl outr (@fpair)}
    {X : Ob C} (h1 h2 : Hom X P),
        h1 == h2 <-> h1 .> outl == h2 .> outl /\ h1 .> outr == h2 .> outr.
Proof.
  split.
  - now intros ->.
  - now intros []; apply fpair_equiv.
Qed.

Section isProduct.

Context
  {C : Cat} {A B : Ob C}
  {P : Ob C} {outl : Hom P A} {outr : Hom P B}
  {fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P}
  {H : isProduct C P outl outr (@fpair)}
  {X : Ob C} [Y : Ob C]
  (f : Hom X A) (g : Hom X B).

Arguments fpair {X} _ _.

#[global] Instance Proper_fpair :
  Proper (equiv ==> equiv ==> equiv) (@fpair X).
Proof.
  intros h1 h1' Heq1 h2 h2' Heq2.
  now rewrite fpair_equiv', !fpair_outl, !fpair_outr.
Defined.

Lemma fpair_universal :
  forall h : Hom X P,
    fpair f g == h <-> f == h .> outl /\ g == h .> outr.
Proof.
  now intros; rewrite fpair_equiv', fpair_outl, fpair_outr.
Qed.

Lemma fpair_unique :
  forall h : Hom X P,
    h .> outl == f -> h .> outr == g -> h == fpair f g.
Proof.
  now intros; rewrite fpair_equiv', fpair_outl, fpair_outr.
Qed.

Lemma fpair_id :
  fpair outl outr == id P.
Proof.
  now rewrite fpair_equiv', fpair_outl, fpair_outr, !comp_id_l.
Qed.

Lemma fpair_pre :
  forall h : Hom Y X,
    fpair (h .> f) (h .> g) == h .> fpair f g.
Proof.
  now intros h; rewrite fpair_equiv', !comp_assoc, !fpair_outl, !fpair_outr.
Qed.

End isProduct.

Class HasProducts (C : Cat) : Type :=
{
  prodOb : Ob C -> Ob C -> Ob C;
  outl : forall {A B : Ob C}, Hom (prodOb A B) A;
  outr : forall {A B : Ob C}, Hom (prodOb A B) B;
  fpair : forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (prodOb A B);
  HasProducts_isProduct :>
    forall {A B : Ob C}, isProduct C (prodOb A B) outl outr (@fpair A B)
}.

Arguments prodOb {C HasProducts} _ _.
Arguments outl   {C HasProducts A B}.
Arguments outr   {C HasProducts A B}.
Arguments fpair  {C HasProducts A B X} _ _.

Ltac fpair := intros; try split;
repeat match goal with
| |- context [fpair (_ .> outl) (_ .> outr)] => rewrite fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite <- fpair_pre
| |- context [fpair _ _ .> outl] => rewrite fpair_outl
| |- context [fpair _ _ .> outr] => rewrite fpair_outr
| |- context [fpair outl outr] => rewrite fpair_id
| |- ?x == ?x => reflexivity
| |- fpair _ _ == _ => apply fpair_equiv
| |- _ == fpair _ _ => apply fpair_equiv
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; auto
end.

Lemma fpair_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A X Y X' Y' : Ob C) (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) == fpair f g .> fpair (outl .> h1) (outr .> h2).
Proof.
  intros; rewrite fpair_equiv'.
  now rewrite !comp_assoc, !fpair_outl, !fpair_outr, <- !comp_assoc, fpair_outl, fpair_outr.
Qed.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : HasProducts C) (A X Y : Ob C) (f : Hom A (prodOb X Y)),
    fpair (f .> outl) (f .> outr) == f.
Proof.
  now intros; rewrite fpair_equiv', fpair_outl, fpair_outr.
Qed.

Lemma isProduct_uiso :
  forall
    (C : Cat) (X Y : Ob C)
    (P1 : Ob C) (outl1 : Hom P1 X) (outr1 : Hom P1 Y)
    (fpair1 : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P1)
    (P2 : Ob C) (outl2 : Hom P2 X) (outr2 : Hom P2 Y)
    (fpair2 : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P2),
      isProduct C P1 outl1 outr1 fpair1 ->
      isProduct C P2 outl2 outr2 fpair2 ->
        exists!! f : Hom P1 P2, isIso f /\ outl1 == f .> outl2 /\ outr1 == f .> outr2.
Proof.
  intros * H1 H2.
  exists (fpair2 _ outl1 outr1); repeat split.
  - exists (fpair1 _ outl2 outr2); split.
    + now rewrite fpair_equiv', !comp_assoc, !comp_id_l, !fpair_outl, !fpair_outr.
    + now rewrite fpair_equiv', !comp_assoc, !comp_id_l, !fpair_outl, !fpair_outr.
  - now rewrite fpair_outl.
  - now rewrite fpair_outr.
  - intros y (HIso & Heql & Heqr).
    now rewrite fpair_equiv', fpair_outl, fpair_outr.
Qed.

Lemma isProduct_iso :
  forall
    (C : Cat) (X Y : Ob C)
    (P1 : Ob C) (outl1 : Hom P1 X) (outr1 : Hom P1 Y)
    (fpair1 : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P1)
    (P2 : Ob C) (outl2 : Hom P2 X) (outr2 : Hom P2 Y)
    (fpair2 : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P2),
      isProduct C P1 outl1 outr1 fpair1 ->
      isProduct C P2 outl2 outr2 fpair2 ->
        P1 ~ P2.
Proof.
  intros. destruct (isProduct_uiso H H0). cat.
Qed.

Lemma isProduct_fpair_equiv :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (outl : Hom P X) (outr : Hom P Y)
    (fpair1 fpair2 : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P),
      isProduct C P outl outr fpair1 ->
      isProduct C P outl outr fpair2 ->
        forall (A : Ob C) (f : Hom A X) (g : Hom A Y),
          fpair1 A f g == fpair2 A f g.
Proof.
  now intros; rewrite fpair_equiv', !fpair_outl, !fpair_outr.
Qed.

Lemma isProduct_outl_equiv
  (C : Cat) (X Y : Ob C)
  (P : Ob C) (outl1 outl2 : Hom P X) (outr : Hom P Y)
  (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P) :
    isProduct C P outl1 outr fpair ->
    isProduct C P outl2 outr fpair ->
      outl1 == outl2.
Proof.
  now intros; rewrite <- fpair_outl, fpair_id, comp_id_l.
Qed.

Lemma isProduct_outr_equiv :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (outl : Hom P X) (outr1 outr2 : Hom P Y)
    (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P),
      isProduct C P outl outr1 fpair ->
      isProduct C P outl outr2 fpair ->
        outr1 == outr2.
Proof.
  now intros; rewrite <- fpair_outr, fpair_id, comp_id_l.
Qed.

Lemma iso_to_prod :
  forall
    (C : Cat) (X Y : Ob C)
    (P Q : Ob C) (outl : Hom P X) (outr : Hom P Y)
    (fpair : forall Q : Ob C, Hom Q X -> Hom Q Y -> Hom Q P),
      isProduct C P outl outr fpair ->
      forall (f : Hom Q P) (H : isIso f),
      isProduct C Q (f .> outl) (f .> outr)
        (fun (A : Ob C) (outl' : Hom A X) (outr' : Hom A Y) =>
          match constructive_indefinite_description _ H with
          | exist _ g _ => fpair A outl' outr' .> g
          end).
Proof.
  intros.
  destruct (constructive_indefinite_description _ _) as (f_inv & eoutl2 & eoutr2).
  constructor; intros.
  - now rewrite comp_assoc, <- (comp_assoc f_inv f), eoutr2, comp_id_l, fpair_outl.
  - now rewrite comp_assoc, <- (comp_assoc f_inv f), eoutr2, comp_id_l, fpair_outr.
  - rewrite <- (comp_id_r _ _ f0), <- (comp_id_r _ _ g), <- !eoutl2, <- !comp_assoc; f_equiv.
    now rewrite fpair_equiv', !comp_assoc.
Qed.

Lemma isProduct_comm :
  forall
    (C : Cat) (X Y P : Ob C) (outl : Hom P X) (outr : Hom P Y)
    (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P),
      isProduct C P outl outr fpair ->
        isProduct C P outr outl (fun A f g => fpair A g f).
Proof.
  intros * []; constructor; cat.
Qed.

Lemma prodOb_comm :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C),
    prodOb X Y ~ prodOb Y X.
Proof.
  intros.
  exists (fpair outr outl), (fpair outr outl).
  fpair.
Qed.

Lemma prodOb_assoc :
  forall (C : Cat) (hp : HasProducts C) (X Y Z : Ob C),
    prodOb X (prodOb Y Z) ~ prodOb (prodOb X Y) Z.
Proof.
  intros.
  exists (fpair (fpair outl (outr .> outl)) (outr .> outr)),
         (fpair (outl .> outl) (fpair (outl .> outr) outr)).
  fpair.
Defined.

Lemma prodOb_assoc' :
  forall (C : Cat) (hp : HasProducts C) (X Y Z : Ob C),
    {f : Hom (prodOb (prodOb X Y) Z) (prodOb X (prodOb Y Z)) | isIso f}.
Proof.
  intros.
  exists (fpair (outl .> outl) (fpair (outl .> outr) outr)),
         (fpair (fpair outl (outr .> outl)) (outr .> outr)).
  fpair.
Defined.

Definition ProductFunctor_fmap
  {C : Cat} {hp : HasProducts C}
  {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
  : Hom (prodOb X X') (prodOb Y Y') :=
    fpair (outl .> f) (outr .> g).

#[export]
Instance Proper_ProductFunctor_fmap :
  forall (C : Cat) (hp : HasProducts C) (X X' Y Y' : Ob C),
    Proper
      ((@equiv _ (HomSetoid X Y))  ==>
      (@equiv _ (HomSetoid X' Y'))  ==>
      (@equiv _ (HomSetoid (prodOb X X') (prodOb Y Y'))))
      (@ProductFunctor_fmap C hp X X' Y Y').
Proof.
  unfold Proper, respectful, ProductFunctor_fmap.
  fpair.
Qed.

Lemma ProductFunctor_fmap_id :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C),
    ProductFunctor_fmap (id X) (id Y) == id (prodOb X Y).
Proof.
  unfold ProductFunctor_fmap.
  fpair.
Defined.

Lemma ProductFunctor_fmap_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A1 A2 B1 B2 C1 C2 : Ob C)
    (f1 : Hom A1 B1) (g1 : Hom B1 C1) (f2 : Hom A2 B2) (g2 : Hom B2 C2),
      ProductFunctor_fmap (f1 .> g1) (f2 .> g2)
        ==
      ProductFunctor_fmap f1 f2 .> ProductFunctor_fmap g1 g2.
Proof.
  unfold ProductFunctor_fmap.
  fpair.
Defined.

Lemma ProductFunctor_fmap_comp_l :
  forall
    {C : Cat} {hp : HasProducts C}
    {X Y Z A : Ob C} (f : Hom X Y) (g : Hom Y Z),
      ProductFunctor_fmap (f .> g) (id A)
        ==
      ProductFunctor_fmap f (id A) .> ProductFunctor_fmap g (id A).
Proof.
  intros. rewrite <- ProductFunctor_fmap_comp.
  fpair.
Defined.

Lemma ProductFunctor_fmap_comp_r :
  forall
    {C : Cat} {hp : HasProducts C}
    {X Y Z A : Ob C} (f : Hom X Y) (g : Hom Y Z),
      ProductFunctor_fmap (id A) (f .> g)
        ==
      ProductFunctor_fmap (id A) f .> ProductFunctor_fmap (id A) g.
Proof.
  intros. rewrite <- ProductFunctor_fmap_comp.
  fpair.
Defined.

#[refine]
#[export]
Instance ProductFunctor {C : Cat} {hp : HasProducts C} : Functor (CAT_prodOb C C) C :=
{
  fob := fun P : Ob (CAT_prodOb C C) => prodOb (fst P) (snd P);
  fmap := fun (X Y : Ob (CAT_prodOb C C)) (f : Hom X Y) => ProductFunctor_fmap (fst f) (snd f)
}.
Proof.
  proper. apply Proper_ProductFunctor_fmap; cat.
  intros. apply ProductFunctor_fmap_comp.
  intros. apply ProductFunctor_fmap_id.
Defined.

Notation "A × B" := (fob ProductFunctor (A, B)) (at level 40).
Notation "f ×' g" := (ProductFunctor_fmap f g) (at level 40).

#[refine]
#[export]
Instance ProductBifunctor {C : Cat} {hp : HasProducts C} : Bifunctor C C C :=
{
  biob := fun X Y : Ob C => prodOb X Y;
  bimap :=
    fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') => fpair (outl .> f) (outr .> g);
}.
Proof.
  all: fpair.
Defined.