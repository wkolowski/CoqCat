From Cat Require Export Cat.

Set Implicit Arguments.

Section Traditional.

Definition isProduct
  (C : Cat) {A B : Ob C}
  (P : Ob C) (outl : Hom P A) (outr : Hom P B)
  (fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P)
  : Prop :=
    forall (X : Ob C) (f : Hom X A) (g : Hom X B),
      setoid_unique (fun u : Hom X P => f == u .> outl /\ g == u .> outr) (fpair f g).

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
  intros. do 2 red in H. do 2 red in H0.
  exists (fpair2 _ outl1 outr1).
  red. repeat split.
    exists (fpair1 _ outl2 outr2).
      destruct
        (H P1 outl1 outr1) as [[HP11 HP12] HP13],
        (H P2 outl2 outr2) as [[HP21 HP22] HP23],
        (H0 P1 outl1 outr1) as [[HP11' HP12'] HP13'],
        (H0 P2 outl2 outr2) as [[HP21' HP22'] HP23'].
      split.
        rewrite <- (HP13 (fpair2 P1 outl1 outr1 .> fpair1 P2 outl2 outr2)).
          apply HP13. cat.
          split; assocr.
            rewrite <- HP21. assumption.
            rewrite <- HP22. assumption.
        rewrite <- (HP23' (fpair1 P2 outl2 outr2 .> fpair2 P1 outl1 outr1)).
          apply HP23'. cat.
          split; assocr.
            rewrite <- HP11'. assumption.
            rewrite <- HP12'. assumption.
    edestruct H0 as [[H1 H2] _]. eauto.
    edestruct H0 as [[H1 H2] _]. eauto.
    intros. destruct H1 as [[y_inv [iso1 iso2]] [eoutl2 eoutr2]].
      edestruct H0. apply H2. cat.
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
  intros. edestruct H, H0. cat.
Qed.

Lemma isProduct_outl_equiv
  (C : Cat) (X Y : Ob C)
  (P : Ob C) (outl1 outl2 : Hom P X) (outr : Hom P Y)
  (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P) :
    isProduct C P outl1 outr fpair ->
    isProduct C P outl2 outr fpair ->
      outl1 == outl2.
Proof.
  intros. do 2 red in H.
  destruct (H P outl1 outr) as [[H1 H2] H3].
  destruct (H0 P outl1 outr) as [[H1' H2'] H3'].
  rewrite (H3 (id P)) in H1'. cat. cat.
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
  intros. do 2 red in H.
  destruct (H P outl outr1) as [[H1 H2] H3].
  destruct (H0 P outl outr1) as [[H1' H2'] H3'].
  rewrite (H3 (id P)) in H2'. cat. cat.
Qed.

(* TODO : Dual *) Lemma iso_to_prod :
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
  unfold isProduct in *. intros.
  destruct (constructive_indefinite_description _ _) as (f_inv & eoutl2 & eoutr2).
  edestruct H as [[H1 H2] H3]. repeat split.
    rewrite comp_assoc, <- (comp_assoc f_inv f).
      rewrite eoutr2. cat.
    rewrite comp_assoc, <- (comp_assoc f_inv f).
      rewrite eoutr2. cat.
    intros. red in H. destruct (H _ f0 g) as [[H1' H2'] H3'].
      specialize (H3' (y .> f)). rewrite H3'; cat.
        rewrite eoutl2. cat.
Qed.

Lemma isProduct_comm :
  forall
    (C : Cat) (X Y P : Ob C) (outl : Hom P X) (outr : Hom P Y)
    (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P),
      isProduct C P outl outr fpair ->
        isProduct C P outr outl (fun A f g => fpair A g f).
Proof.
  unfold isProduct in *; intros.
  destruct (H X0 g f) as [[H1 H2] H3]. cat.
Qed.

End Traditional.

Class HasProducts (C : Cat) : Type :=
{
  product : Ob C -> Ob C -> Ob C;
  outl : forall {A B : Ob C}, Hom (product A B) A;
  outr : forall {A B : Ob C}, Hom (product A B) B;
  fpair : forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (product A B);
  Proper_fpair :> forall (A B X : Ob C), Proper (equiv ==> equiv ==> equiv) (@fpair A B X);
  is_product :
    forall (A B : Ob C), isProduct C (product A B) outl outr (@fpair A B)
}.

Arguments product {C HasProducts} _ _.
Arguments outl   {C HasProducts A B}.
Arguments outr   {C HasProducts A B}.
Arguments fpair  {C HasProducts A B X} _ _.

Lemma fpair_universal :
  forall
    {C : Cat} {hp : HasProducts C}
    {A B X : Ob C} (f : Hom X A) (g : Hom X B) (h : Hom X (product A B)),
      fpair f g == h <-> f == h .> outl /\ g == h .> outr.
Proof.
  intros C hp A B X f g h.
  split.
  - intros <-.
    destruct (is_product A B X f g) as [[H11 H12] H2].
    split; assumption.
  - intros [-> ->].
    destruct (is_product A B X (h .> outl) (h .> outr)) as [[H11 H12] H2].
    apply H2.
    split; reflexivity.
Qed.

Section HasProducts.

Context
  [C : Cat] [hp : HasProducts C]
  [A B X Y : Ob C]
  (f : Hom X A) (g : Hom X B).

Lemma fpair_outl :
  fpair f g .> outl == f.
Proof.
  destruct (fpair_universal f g (fpair f g)) as [[<- _] _]; reflexivity.
Qed.

Lemma fpair_outr :
  fpair f g .> outr == g.
Proof.
  destruct (fpair_universal f g (fpair f g)) as [[_ <-] _]; reflexivity.
Qed.

Lemma fpair_unique :
  forall h : Hom X (product A B),
    h .> outl == f -> h .> outr == g -> h == fpair f g.
Proof.
  intros h Heoutl2 Heoutr2.
  symmetry.
  apply fpair_universal.
  split; symmetry; assumption.
Qed.

Lemma fpair_id :
  fpair outl outr == id (product A B).
Proof.
  rewrite fpair_universal, !comp_id_l.
  split; reflexivity.
Qed.

Lemma fpair_pre :
  forall h : Hom Y X,
    fpair (h .> f) (h .> g) == h .> fpair f g.
Proof.
  intros h.
  rewrite fpair_universal, !comp_assoc, fpair_outl, fpair_outr.
  split; reflexivity.
Qed.

End HasProducts.

Ltac fpair := intros; try split;
repeat match goal with
| |- context [fpair (_ .> outl) (_ .> outr)] => rewrite fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite <- fpair_pre
| |- context [fpair _ _ .> outl] => rewrite fpair_outl
| |- context [fpair _ _ .> outr] => rewrite fpair_outr
| |- context [fpair outl outr] => rewrite fpair_id
| |- ?x == ?x => reflexivity
| |- fpair _ _ == fpair _ _ => apply Proper_fpair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- fpair _ _ == id (product _ _) => rewrite <- fpair_id; apply Proper_fpair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; auto
end.

Lemma fpair_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A X Y X' Y' : Ob C) (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) == fpair f g .> fpair (outl .> h1) (outr .> h2).
Proof. fpair. Qed.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : HasProducts C) (A X Y : Ob C) (f : Hom A (product X Y)),
    fpair (f .> outl) (f .> outr) == f.
Proof. fpair. Qed.

Lemma fpair_equiv :
  forall
    {C : Cat} {hp : HasProducts C}
    {A B X : Ob C} (h1 h2 : Hom X (product A B)),
      h1 .> outl == h2 .> outl -> h1 .> outr == h2 .> outr -> h1 == h2.
Proof.
  intros C hp A B X h1 h2 Heq1 Heq2.
  rewrite <- (fpair_pre_id _ _ _ _ h2).
  apply fpair_unique; assumption.
Qed.

Lemma product_comm :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C),
    product X Y ~ product Y X.
Proof.
  intros.
  red. exists (fpair outr outl).
  red. exists (fpair outr outl).
  fpair.
Qed.

Lemma product_assoc :
  forall (C : Cat) (hp : HasProducts C) (X Y Z : Ob C),
    product X (product Y Z) ~ product (product X Y) Z.
Proof.
  intros.
  red. exists (fpair (fpair outl (outr .> outl)) (outr .> outr)).
  red. exists (fpair (outl .> outl) (fpair (outl .> outr) outr)).
  fpair.
Defined.

Lemma product_assoc' :
  forall (C : Cat) (hp : HasProducts C) (X Y Z : Ob C),
    {f : Hom (product (product X Y) Z) (product X (product Y Z)) | isIso f}.
Proof.
  intros.
  exists (fpair (outl .> outl) (fpair (outl .> outr) outr)).
  exists (fpair (fpair outl (outr .> outl)) (outr .> outr)).
  fpair.
Defined.

Definition ProductFunctor_fmap
  {C : Cat} {hp : HasProducts C}
  {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
  : Hom (product X X') (product Y Y') :=
    fpair (outl .> f) (outr .> g).

#[export]
Instance Proper_ProductFunctor_fmap :
  forall (C : Cat) (hp : HasProducts C) (X X' Y Y' : Ob C),
    Proper
      ((@equiv _ (HomSetoid X Y))  ==>
      (@equiv _ (HomSetoid X' Y'))  ==>
      (@equiv _ (HomSetoid (product X X') (product Y Y'))))
      (@ProductFunctor_fmap C hp X X' Y Y').
Proof.
  unfold Proper, respectful, ProductFunctor_fmap.
  fpair.
Qed.

Lemma ProductFunctor_fmap_id :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C),
    ProductFunctor_fmap (id X) (id Y) == id (product X Y).
Proof.
  unfold ProductFunctor_fmap.
  fpair.
Defined.

Lemma ProductFunctor_fmap_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A1 A2 B1 B2 C1 C2 : Ob C) (f1 : Hom A1 B1) (g1 : Hom B1 C1) (f2 : Hom A2 B2) (g2 : Hom B2 C2),
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
    {X Y : Ob C} (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
      ProductFunctor_fmap (f .> g) (id Z)
        == 
      ProductFunctor_fmap f (id Z) .> ProductFunctor_fmap g (id Z).
Proof.
  intros. rewrite <- ProductFunctor_fmap_comp.
  fpair.
Defined.

Lemma ProductFunctor_fmap_comp_r :
  forall
    {C : Cat} {hp : HasProducts C}
    {X Y : Ob C} (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
      ProductFunctor_fmap (id Z) (f .> g)
        ==
      ProductFunctor_fmap (id Z) f .> ProductFunctor_fmap (id Z) g.
Proof.
  intros. rewrite <- ProductFunctor_fmap_comp.
  fpair.
Defined.

#[refine]
#[export]
Instance ProductFunctor {C : Cat} {hp : HasProducts C} : Functor (CAT_product C C) C :=
{
  fob := fun P : Ob (CAT_product C C) => product (fst P) (snd P);
  fmap := fun (X Y : Ob (CAT_product C C)) (f : Hom X Y) => ProductFunctor_fmap (fst f) (snd f)
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
  biob := fun X Y : Ob C => product X Y;
  bimap :=
    fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') => fpair (outl .> f) (outr .> g);
}.
Proof.
  unfold Proper, respectful. all: fpair.
Defined.

Module Wut.

Set Warnings "-require-in-module".
From Cat Require Export Tactics.FunctorTactic.
Set Warnings "require-in-module".

#[refine]
#[export]
Instance Simplify_fpair_outl
  (C : Cat) (hp : HasProducts C) (X Y Z : Ob C) (f : Hom X Y) (g : Hom X Z)
  : Simplify (Comp (Var (fpair f g)) (Var outl)) | 1 :=
{
  simplify := Var f
}.
Proof.
  cbn. rewrite fpair_outl. reflexivity.
Defined.

#[refine]
#[export]
Instance Simplify_fpair_outr
  (C : Cat) (hp : HasProducts C) (X Y Z : Ob C) (f : Hom X Y) (g : Hom X Z)
  : Simplify (Comp (Var (fpair f g)) (Var outr)) | 1 :=
{
  simplify := Var g
}.
Proof.
  cbn. rewrite fpair_outr. reflexivity.
Defined.

#[refine]
#[export]
Instance Simplify_fpair_id
  (C : Cat) (hp : HasProducts C) (X Y Z : Ob C) (f : Hom X Y) (g : Hom X Z)
  : Simplify (Var (fpair outl outr)) | 1 :=
{
  simplify := Id (product X Y)
}.
Proof.
  cbn. rewrite fpair_id. reflexivity.
Defined.

Goal
  forall (C : Cat) (hp : HasProducts C) (X Y Z : Ob C),
    fpair (@outl _ _ X Y) outr .> outl == outl.
Proof.
  intros. reflect_cat. reflexivity.
Qed.

End Wut.

Module Tactic.

Inductive exp {C : Cat} {hp : HasProducts C} : Ob C -> Ob C -> Type :=
| Id    : forall X : Ob C, exp X X
| Var   : forall X Y : Ob C, Hom X Y -> exp X Y
| Comp  : forall X Y Z : Ob C, exp X Y -> exp Y Z -> exp X Z
| Proj1 : forall X Y : Ob C, exp (product X Y) X
| Proj2 : forall X Y : Ob C, exp (product X Y) Y
| Fpair : forall A B X : Ob C, exp X A -> exp X B -> exp X (product A B).

Arguments Id    {C hp} _.
Arguments Var   {C hp X Y} _.
Arguments Comp  {C hp X Y Z} _ _.
Arguments Proj1 {C hp X Y}.
Arguments Proj2 {C hp X Y}.
Arguments Fpair {C hp A B X} _ _.

Fixpoint expDenote {C : Cat} {hp : HasProducts C} {X Y : Ob C} (e : exp X Y) : Hom X Y :=
match e with
| Id X        => id X
| Var f       => f
| Comp e1 e2  => expDenote e1 .> expDenote e2
| Proj1       => outl
| Proj2       => outr
| Fpair e1 e2 => fpair (expDenote e1) (expDenote e2)
end.

(* TODO: class-based simplification *)

End Tactic.

Module Universal.

Class HasProducts (C : Cat) : Type :=
{
  product : Ob C -> Ob C -> Ob C;
  outl : forall {A B : Ob C}, Hom (product A B) A;
  outr : forall {A B : Ob C}, Hom (product A B) B;
  fpair : forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (product A B);
  Proper_fpair :> forall (A B X : Ob C), Proper (equiv ==> equiv ==> equiv) (@fpair A B X);
  fpair_universal :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B) (h : Hom X (product A B)),
      fpair f g == h <-> f == h .> outl /\ g == h .> outr
}.

Arguments product {C HasProducts} _ _.
Arguments outl   {C HasProducts A B}.
Arguments outr   {C HasProducts A B}.
Arguments fpair  {C HasProducts A B X} _ _.

Section HasProducts.

Context
  [C : Cat] [hp : HasProducts C]
  [A B X Y : Ob C]
  (f : Hom X A) (g : Hom X B).

Lemma fpair_outl :
  fpair f g .> outl == f.
Proof.
  destruct (fpair_universal f g (fpair f g)) as [[<- _] _]; reflexivity.
Qed.

Lemma fpair_outr :
  fpair f g .> outr == g.
Proof.
  destruct (fpair_universal f g (fpair f g)) as [[_ <-] _]; reflexivity.
Qed.

Lemma fpair_unique :
  forall h : Hom X (product A B),
    h .> outl == f -> h .> outr == g -> h == fpair f g.
Proof.
  intros h Heoutl2 Heoutr2.
  symmetry.
  apply fpair_universal.
  split; symmetry; assumption.
Qed.

Lemma fpair_id :
  fpair outl outr == id (product A B).
Proof.
  rewrite fpair_universal, !comp_id_l.
  split; reflexivity.
Qed.

Lemma fpair_pre :
  forall h : Hom Y X,
    fpair (h .> f) (h .> g) == h .> fpair f g.
Proof.
  intros h.
  rewrite fpair_universal, !comp_assoc, fpair_outl, fpair_outr.
  split; reflexivity.
Qed.

End HasProducts.

Ltac fpair := repeat (intros; try split;
match goal with
| |- context [fpair _ _ == _] => rewrite fpair_universal
| H : fpair _ _ == _ |- _ => rewrite fpair_universal in H
| |- context [fpair (_ .> outl) (_ .> outr)] => rewrite fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite <- fpair_pre
| |- context [fpair _ _ .> outl] => rewrite fpair_outl
| |- context [fpair _ _ .> outr] => rewrite fpair_outr
| |- context [fpair outl outr] => rewrite fpair_id
| |- ?x == ?x => reflexivity
| |- fpair _ _ == fpair _ _ => apply Proper_fpair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- fpair _ _ == id (product _ _) => rewrite <- fpair_id; apply Proper_fpair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; auto
end).

Lemma fpair_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A X Y X' Y' : Ob C) (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) == fpair f g .> fpair (outl .> h1) (outr .> h2).
Proof. fpair. Qed.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : HasProducts C) (A X Y : Ob C) (f : Hom A (product X Y)),
    fpair (f .> outl) (f .> outr) == f.
Proof. fpair. Qed.

End Universal.

Module UniversalEquiv.

#[refine]
#[export]
Instance to (C : Cat) (hp : HasProducts C) : Universal.HasProducts C :=
{
  product := @product C hp;
  outl := @outl C hp;
  outr := @outr C hp;
  fpair := @fpair C hp;
}.
Proof.
  apply @fpair_universal.
Defined.

#[refine]
#[export]
Instance from (C : Cat) (hp : Universal.HasProducts C) : HasProducts C :=
{
  product := @Universal.product C hp;
  outl := @Universal.outl C hp;
  outr := @Universal.outr C hp;
  fpair := @Universal.fpair C hp;
}.
Proof.
  unfold isProduct, setoid_unique.
  intros A B X f g; split.
  - Universal.fpair.
  - intros h [-> ->]. Universal.fpair.
Defined.

End UniversalEquiv.

Module Rules.

Class HasProducts (C : Cat) : Type :=
{
  product : Ob C -> Ob C -> Ob C;
  outl : forall {A B : Ob C}, Hom (product A B) A;
  outr : forall {A B : Ob C}, Hom (product A B) B;
  fpair :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (product A B);
  Proper_fpair :>
    forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@fpair A B X);
  fpair_outl :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B),
      fpair f g .> outl == f;
  fpair_outr :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B),
      fpair f g .> outr == g;
  fpair_unique :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B) (h : Hom X (product A B)),
      h .> outl == f -> h .> outr == g -> h == fpair f g;
}.

Arguments product {C HasProducts} _ _.
Arguments outl   {C HasProducts A B}.
Arguments outr   {C HasProducts A B}.
Arguments fpair  {C HasProducts A B X} _ _.

Section HasProducts.

Context
  [C : Cat] [hp : HasProducts C]
  [A B X Y : Ob C]
  (f : Hom X A) (g : Hom X B).

Lemma fpair_universal :
  forall h : Hom X (product A B),
    fpair f g == h <-> f == h .> outl /\ g == h .> outr.
Proof.
  split.
  - intros <-. rewrite fpair_outl, fpair_outr. split; reflexivity.
  - intros [-> ->]. symmetry; apply fpair_unique; reflexivity.
Qed.

Lemma fpair_id :
  fpair outl outr == id (product A B).
Proof.
  symmetry; apply fpair_unique; rewrite comp_id_l; reflexivity.
Qed.

Lemma fpair_pre :
  forall h : Hom Y X,
    fpair (h .> f) (h .> g) == h .> fpair f g.
Proof.
  intros h.
  symmetry; apply fpair_unique.
  - rewrite comp_assoc, fpair_outl. reflexivity.
  - rewrite comp_assoc, fpair_outr. reflexivity.
Qed.

End HasProducts.

Ltac fpair := repeat (intros; try split;
match goal with
| |- context [fpair _ _ == _] => rewrite fpair_universal
| H : fpair _ _ == _ |- _ => rewrite fpair_universal in H
| |- context [fpair (_ .> outl) (_ .> outr)] => rewrite fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite <- fpair_pre
| |- context [fpair _ _ .> outl] => rewrite fpair_outl
| |- context [fpair _ _ .> outr] => rewrite fpair_outr
| |- context [fpair outl outr] => rewrite fpair_id
| |- ?x == ?x => reflexivity
| |- fpair _ _ == fpair _ _ => apply Proper_fpair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- fpair _ _ == id (product _ _) => rewrite <- fpair_id; apply Proper_fpair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; auto
end).

Lemma fpair_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A X Y X' Y' : Ob C) (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) == fpair f g .> fpair (outl .> h1) (outr .> h2).
Proof. fpair. Qed.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : HasProducts C) (A X Y : Ob C) (f : Hom A (product X Y)),
    fpair (f .> outl) (f .> outr) == f.
Proof. fpair. Qed.

End Rules.

Module RulesEquiv.

#[refine]
#[export]
Instance to (C : Cat) (hp : HasProducts C) : Rules.HasProducts C :=
{
  product := @product C hp;
  outl := @outl C hp;
  outr := @outr C hp;
  fpair := @fpair C hp;
}.
Proof.
  - fpair.
  - fpair.
  - intros A B X f g h <- <-. fpair.
Defined.

#[refine]
#[export]
Instance from (C : Cat) (hp : Rules.HasProducts C) : HasProducts C :=
{
  product := @Rules.product C hp;
  outl := @Rules.outl C hp;
  outr := @Rules.outr C hp;
  fpair := @Rules.fpair C hp;
}.
Proof.
  unfold isProduct, setoid_unique.
  intros A B X f g; split.
  - Rules.fpair.
  - intros y [-> ->]. Rules.fpair.
Defined.

End RulesEquiv.

Module Rules2.

Class HasProducts (C : Cat) : Type :=
{
  product : Ob C -> Ob C -> Ob C;
  outl : forall {A B : Ob C}, Hom (product A B) A;
  outr : forall {A B : Ob C}, Hom (product A B) B;
  fpair :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (product A B);
  Proper_fpair :>
    forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@fpair A B X);
(* reflection *)
  fpair_id :
    forall X Y : Ob C,
      fpair outl outr == id (product X Y);
(* cancellation *)
  fpair_outl :
    forall (X Y A : Ob C) (f : Hom A X) (g : Hom A Y),
      fpair f g .> outl == f;
  fpair_outr :
    forall (X Y A : Ob C) (f : Hom A X) (g : Hom A Y),
      fpair f g .> outr == g;
(* fusion *)
  fpair_pre :
    forall (A B X Y : Ob C) (f : Hom A B) (g1 : Hom B X) (g2 : Hom B Y),
      fpair (f .> g1) (f .> g2) == f .> fpair g1 g2
}.

Arguments product {C HasProducts} _ _.
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
| |- fpair _ _ == fpair _ _ => apply Proper_fpair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- fpair _ _ == id (product _ _) => rewrite <- fpair_id; apply Proper_fpair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; auto
end.

Section HasProducts.

Context
  [C : Cat] [hp : HasProducts C]
  [A B X Y : Ob C]
  (f : Hom X A) (g : Hom X B).

Lemma fpair_universal :
  forall h : Hom X (product A B),
    fpair f g == h <-> f == h .> outl /\ g == h .> outr.
Proof.
  split.
  - intros <-. fpair.
  - intros [-> ->]. fpair.
Qed.

End HasProducts.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : HasProducts C) (A X Y : Ob C) (f : Hom A (product X Y)),
    fpair (f .> outl) (f .> outr) == f.
Proof. fpair. Qed.

Lemma fpair_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A X Y X' Y' : Ob C) (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) == fpair f g .> fpair (outl .> h1) (outr .> h2).
Proof. fpair. Qed.

End Rules2.

Module Rules2Equiv.

#[refine]
#[export]
Instance to (C : Cat) (hp : HasProducts C) : Rules2.HasProducts C :=
{
  product := @product C hp;
  outl := @outl C hp;
  outr := @outr C hp;
  fpair := @fpair C hp;
}.
Proof. all: fpair. Defined.

#[refine]
#[export]
Instance from (C : Cat) (hp : Rules2.HasProducts C) : HasProducts C :=
{
  product := @Rules2.product C hp;
  outl := @Rules2.outl C hp;
  outr := @Rules2.outr C hp;
  fpair := @Rules2.fpair C hp;
}.
Proof.
  unfold isProduct, setoid_unique.
  intros A B X f g; split.
  - Rules2.fpair.
  - intros y [-> ->]. Rules2.fpair.
Defined.

End Rules2Equiv.

Module Rules3.

Class HasProducts (C : Cat) : Type :=
{
  product : Ob C -> Ob C -> Ob C;
  outl : forall {A B : Ob C}, Hom (product A B) A;
  outr : forall {A B : Ob C}, Hom (product A B) B;
  fpair :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (product A B);
(*   Proper_fpair :>
    forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@fpair A B X); *)
  fpair_outl :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B),
      fpair f g .> outl == f;
  fpair_outr :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B),
      fpair f g .> outr == g;
  fpair_equiv :
    forall {A B X : Ob C} (f g : Hom X (product A B)),
      f .> outl == g .> outl -> f .> outr == g .> outr -> f == g
}.

Arguments product {C HasProducts} _ _.
Arguments outl   {C HasProducts A B}.
Arguments outr   {C HasProducts A B}.
Arguments fpair  {C HasProducts A B X} _ _.

Section HasProducts.

Context
  [C : Cat] [hp : HasProducts C]
  [A B X Y : Ob C]
  (f : Hom X A) (g : Hom X B).

Instance Proper_fpair :
  Proper (equiv ==> equiv ==> equiv) (@fpair C hp X A B).
Proof.
  intros h1 h1' Heq1 h2 h2' Heq2.
  apply fpair_equiv.
  - rewrite !fpair_outl. assumption.
  - rewrite !fpair_outr. assumption.
Defined.

Lemma fpair_universal :
  forall h : Hom X (product A B),
    fpair f g == h <-> f == h .> outl /\ g == h .> outr.
Proof.
  split.
  - intros <-. rewrite fpair_outl, fpair_outr. split; reflexivity.
  - intros [Hf Hg].
    apply fpair_equiv.
    + rewrite fpair_outl; assumption.
    + rewrite fpair_outr; assumption.
Qed.

Lemma fpair_unique :
  forall h : Hom X (product A B),
    f == h .> outl -> g == h .> outr -> h == fpair f g.
Proof.
  intros h Hf Hg.
  symmetry; rewrite fpair_universal.
  split; assumption.
Qed.

Lemma fpair_id :
  fpair outl outr == id (product A B).
Proof.
  apply fpair_equiv.
  - rewrite fpair_outl, comp_id_l; reflexivity.
  - rewrite fpair_outr, comp_id_l; reflexivity.
Qed.

Lemma fpair_pre :
  forall h : Hom Y X,
    fpair (h .> f) (h .> g) == h .> fpair f g.
Proof.
  intros h.
  apply fpair_equiv.
  - rewrite comp_assoc, !fpair_outl; reflexivity.
  - rewrite comp_assoc, !fpair_outr; reflexivity.
Qed.

End HasProducts.

Ltac fpair := repeat (intros; try split;
match goal with
| |- context [fpair _ _ == _] => rewrite fpair_universal
| H : fpair _ _ == _ |- _ => rewrite fpair_universal in H
| |- context [fpair (_ .> outl) (_ .> outr)] => rewrite fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite <- fpair_pre
| |- context [fpair _ _ .> outl] => rewrite fpair_outl
| |- context [fpair _ _ .> outr] => rewrite fpair_outr
| |- context [fpair outl outr] => rewrite fpair_id
| |- ?x == ?x => reflexivity
| |- fpair _ _ == fpair _ _ => apply Proper_fpair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- fpair _ _ == id (product _ _) => rewrite <- fpair_id; apply Proper_fpair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; auto
end).

Lemma fpair_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A X Y X' Y' : Ob C) (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) == fpair f g .> fpair (outl .> h1) (outr .> h2).
Proof. fpair. Qed.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : HasProducts C) (A X Y : Ob C) (f : Hom A (product X Y)),
    fpair (f .> outl) (f .> outr) == f.
Proof. fpair. Qed.

End Rules3.

Module Rules3Equiv.

#[refine]
#[export]
Instance to (C : Cat) (hp : HasProducts C) : Rules3.HasProducts C :=
{
  product := @product C hp;
  outl := @outl C hp;
  outr := @outr C hp;
  fpair := @fpair C hp;
}.
Proof.
  - apply fpair_outl.
  - apply fpair_outr.
  - intros A B X f g Hf Hg.
    apply fpair_equiv; assumption.
Defined.

#[refine]
#[export]
Instance from (C : Cat) (hp : Rules3.HasProducts C) : HasProducts C :=
{
  product := @Rules3.product C hp;
  outl := @Rules3.outl C hp;
  outr := @Rules3.outr C hp;
  fpair := @Rules3.fpair C hp;
}.
Proof.
  - cat. Rules3.fpair.
  - unfold isProduct, setoid_unique.
    intros A B X f g; split.
    + Rules3.fpair.
    + intros y [Hf Hg]. symmetry; apply Rules3.fpair_unique; assumption.
Defined.

End Rules3Equiv.