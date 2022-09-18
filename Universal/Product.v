From Cat Require Export Cat.

Set Implicit Arguments.

Class isProduct
  (C : Cat) {A B : Ob C}
  (P : Ob C) (outl : Hom P A) (outr : Hom P B)
  (fpair : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ P)
  : Prop :=
{
  fpair_outl :
    forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B),
      fpair a b .> outl == a;
  fpair_outr :
    forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B),
      fpair a b .> outr == b;
  equiv_product :
    forall {Γ : Ob C} (x y : Hom Γ P),
      x .> outl == y .> outl -> x .> outr == y .> outr -> x == y
}.

#[export] Hint Mode isProduct ! ! ! ! ! ! ! : core.
#[export] Hint Mode isProduct ! ! ! - - - - : core.

Lemma equiv_product' :
  forall
    {C : Cat} {A B : Ob C}
    {P : Ob C} {outl : Hom P A} {outr : Hom P B}
    {fpair : forall {Γ : Ob C} (f : Hom Γ A) (g : Hom Γ B), Hom Γ P}
    {isP : isProduct C P outl outr (@fpair)}
    {Γ : Ob C} (h1 h2 : Hom Γ P),
      h1 == h2 <-> h1 .> outl == h2 .> outl /\ h1 .> outr == h2 .> outr.
Proof.
  split.
  - now intros ->.
  - now intros []; apply equiv_product.
Qed.

Section isProduct.

Context
  {C : Cat} {A B : Ob C}
  {P : Ob C} {outl : Hom P A} {outr : Hom P B}
  {fpair : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ P}
  {H : isProduct C P outl outr (@fpair)}
  {Γ : Ob C} [Y : Ob C]
  (a : Hom Γ A) (b : Hom Γ B).

Arguments fpair {Γ} _ _.

#[global] Instance Proper_fpair :
  Proper (equiv ==> equiv ==> equiv) (@fpair Γ).
Proof.
  intros h1 h1' Heq1 h2 h2' Heq2.
  now rewrite equiv_product', !fpair_outl, !fpair_outr.
Defined.

Lemma fpair_universal :
  forall p : Hom Γ P,
    fpair a b == p <-> a == p .> outl /\ b == p .> outr.
Proof.
  now intros; rewrite equiv_product', fpair_outl, fpair_outr.
Qed.

Lemma fpair_unique :
  forall p : Hom Γ P,
    p .> outl == a -> p .> outr == b -> p == fpair a b.
Proof.
  now intros; rewrite equiv_product', fpair_outl, fpair_outr.
Qed.

Lemma fpair_id :
  fpair outl outr == id P.
Proof.
  now rewrite equiv_product', fpair_outl, fpair_outr, !comp_id_l.
Qed.

Lemma fpair_pre :
  forall f : Hom Y Γ,
    f .> fpair a b == fpair (f .> a) (f .> b).
Proof.
  now intros h; rewrite equiv_product', !comp_assoc, !fpair_outl, !fpair_outr.
Qed.

End isProduct.

Ltac product_simpl :=
  repeat (rewrite
    ?equiv_product', ?fpair_outl, ?fpair_outr, ?fpair_id, ?fpair_pre,
    ?comp_id_l, ?comp_id_r, <- ?comp_assoc).

Lemma isProduct_uiso :
  forall
    (C : Cat) (A B : Ob C)
    (P1 : Ob C) (outl1 : Hom P1 A) (outr1 : Hom P1 B)
    (fpair1 : forall (Γ : Ob C) (f : Hom Γ A) (g : Hom Γ B), Hom Γ P1)
    (P2 : Ob C) (outl2 : Hom P2 A) (outr2 : Hom P2 B)
    (fpair2 : forall (Γ : Ob C) (f : Hom Γ A) (g : Hom Γ B), Hom Γ P2),
      isProduct C P1 outl1 outr1 fpair1 ->
      isProduct C P2 outl2 outr2 fpair2 ->
        exists!! f : Hom P1 P2, isIso f /\ outl1 == f .> outl2 /\ outr1 == f .> outr2.
Proof.
  intros * H1 H2.
  exists (fpair2 _ outl1 outr1); repeat split.
  - exists (fpair1 _ outl2 outr2); split.
    + now rewrite equiv_product', !comp_assoc, !comp_id_l, !fpair_outl, !fpair_outr.
    + now rewrite equiv_product', !comp_assoc, !comp_id_l, !fpair_outl, !fpair_outr.
  - now rewrite fpair_outl.
  - now rewrite fpair_outr.
  - intros y (HIso & Heql & Heqr).
    now rewrite equiv_product', fpair_outl, fpair_outr.
Qed.

Lemma isProduct_iso :
  forall
    (C : Cat) (A B : Ob C)
    (P1 : Ob C) (outl1 : Hom P1 A) (outr1 : Hom P1 B)
    (fpair1 : forall (Γ : Ob C) (f : Hom Γ A) (g : Hom Γ B), Hom Γ P1)
    (P2 : Ob C) (outl2 : Hom P2 A) (outr2 : Hom P2 B)
    (fpair2 : forall (Γ : Ob C) (f : Hom Γ A) (g : Hom Γ B), Hom Γ P2),
      isProduct C P1 outl1 outr1 fpair1 ->
      isProduct C P2 outl2 outr2 fpair2 ->
        P1 ~ P2.
Proof.
  intros. destruct (isProduct_uiso H H0). cat.
Qed.

Lemma isProduct_equiv_fpair :
  forall
    (C : Cat) (A B : Ob C)
    (P : Ob C) (outl : Hom P A) (outr : Hom P B)
    (fpair1 fpair2 : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ P),
      isProduct C P outl outr (@fpair1) ->
      isProduct C P outl outr (@fpair2) ->
        forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B),
          fpair1 a b == fpair2 a b.
Proof.
  now intros; rewrite equiv_product', !fpair_outl, !fpair_outr.
Qed.

Lemma isProduct_equiv_outl :
  forall
    (C : Cat) (A B : Ob C)
    (P : Ob C) (outl1 outl2 : Hom P A) (outr : Hom P B)
    (fpair : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ P),
      isProduct C P outl1 outr (@fpair) ->
      isProduct C P outl2 outr (@fpair) ->
        outl1 == outl2.
Proof.
  now intros; rewrite <- fpair_outl, fpair_id, comp_id_l.
Qed.

Lemma isProduct_equiv_outr :
  forall
    (C : Cat) (A B : Ob C)
    (P : Ob C) (outl : Hom P A) (outr1 outr2 : Hom P B)
    (fpair : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ P),
      isProduct C P outl outr1 (@fpair) ->
      isProduct C P outl outr2 (@fpair) ->
        outr1 == outr2.
Proof.
  now intros; rewrite <- fpair_outr, fpair_id, comp_id_l.
Qed.

Lemma iso_to_product : (* TODO: dual *)
  forall
    (C : Cat) (A B : Ob C)
    (P : Ob C) (outl : Hom P A) (outr : Hom P B)
    (fpair : forall {Γ : Ob C}, Hom Γ A -> Hom Γ B -> Hom Γ P),
      isProduct C P outl outr (@fpair) ->
      forall (Q : Ob C) (f : Hom Q P) (H : isIso f),
      isProduct C Q (f .> outl) (f .> outr)
        (fun (Γ : Ob C) (a : Hom Γ A) (b : Hom Γ B) =>
          match constructive_indefinite_description _ H with
          | exist _ g _ => fpair a b .> g
          end).
Proof.
  intros.
  destruct (constructive_indefinite_description _ _) as (f_inv & eoutl2 & eoutr2).
  constructor; intros.
  - now rewrite comp_assoc, <- (comp_assoc f_inv f), eoutr2, comp_id_l, fpair_outl.
  - now rewrite comp_assoc, <- (comp_assoc f_inv f), eoutr2, comp_id_l, fpair_outr.
  - rewrite <- (comp_id_r _ _ x), <- (comp_id_r _ _ y), <- !eoutl2, <- !comp_assoc; f_equiv.
    now rewrite equiv_product', !comp_assoc.
Qed.

Lemma isProduct_comm :
  forall
    {C : Cat} {A B : Ob C}
    {P : Ob C} {outl : Hom P A} {outr : Hom P B}
    {fpair : forall {Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ P},
      isProduct C P outl outr (@fpair) ->
        isProduct C P outr outl (fun Γ a b => fpair b a).
Proof.
  intros * []; constructor; cat.
Qed.

Class HasProducts (C : Cat) : Type :=
{
  product : Ob C -> Ob C -> Ob C;
  outl : forall {A B : Ob C}, Hom (product A B) A;
  outr : forall {A B : Ob C}, Hom (product A B) B;
  fpair : forall {A B Γ : Ob C} (a : Hom Γ A) (b : Hom Γ B), Hom Γ (product A B);
  isProduct_HasProducts' :>
    forall {A B : Ob C}, isProduct C (product A B) outl outr (@fpair A B)
}.

Arguments product {C _} _ _.
Arguments outl    {C _ A B}.
Arguments outr    {C _ A B}.
Arguments fpair   {C _ A B Γ} _ _.

Ltac solve_product := intros; try split;
repeat match goal with
| |- context [fpair (_ .> outl) (_ .> outr)] => rewrite <- fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite fpair_pre
| |- context [fpair _ _ .> outl] => rewrite fpair_outl
| |- context [fpair _ _ .> outr] => rewrite fpair_outr
| |- context [fpair outl outr] => rewrite fpair_id
| |- ?x == ?x => reflexivity
| |- fpair _ _ == _ => apply equiv_product
| |- _ == fpair _ _ => apply equiv_product
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; auto
end.

Ltac product_simpl' :=
repeat match goal with
| |- context [fpair (_ .> outl) (_ .> outr)] => rewrite <- fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite fpair_pre
| |- context [fpair _ _ .> outl] => rewrite fpair_outl
| |- context [fpair _ _ .> outr] => rewrite fpair_outr
| |- context [fpair outl outr] => rewrite fpair_id
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| H : context [fpair (_ .> outl) (_ .> outr)] |- _ => rewrite <- fpair_pre, fpair_id in H
| H : context [_ .> fpair _ _] |- _ => rewrite fpair_pre in H
| H : context [fpair _ _ .> outl] |- _ => rewrite fpair_outl in H
| H : context [fpair _ _ .> outr] |- _ => rewrite fpair_outr in H
| H : context [fpair outl outr] |- _ => rewrite fpair_id in H
| H : context [id _ .> _] |- _ => rewrite comp_id_l in H
| H : context [_ .> id _] |- _ => rewrite comp_id_r in H
| _ => rewrite <- ?comp_assoc
end.

Lemma fpair_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A B Γ A' B' : Ob C) (a : Hom Γ A) (b : Hom Γ B) (h1 : Hom A A') (h2 : Hom B B'),
      fpair (a .> h1) (b .> h2) == fpair a b .> fpair (outl .> h1) (outr .> h2).
Proof.
  intros; rewrite equiv_product'.
  now rewrite !comp_assoc, !fpair_outl, !fpair_outr, <- !comp_assoc, fpair_outl, fpair_outr.
Qed.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : HasProducts C) (A B Γ : Ob C) (p : Hom Γ (product A B)),
    fpair (p .> outl) (p .> outr) == p.
Proof.
  now intros; rewrite equiv_product', fpair_outl, fpair_outr.
Qed.

Lemma product_comm :
  forall (C : Cat) (hp : HasProducts C) (A B : Ob C),
    product A B ~ product B A.
Proof.
  red; intros.
  exists (fpair outr outl), (fpair outr outl).
  solve_product.
Qed.

Lemma product_assoc :
  forall (C : Cat) (hp : HasProducts C) (A B C : Ob C),
    product A (product B C) ~ product (product A B) C.
Proof.
  intros.
  exists (fpair (fpair outl (outr .> outl)) (outr .> outr)),
         (fpair (outl .> outl) (fpair (outl .> outr) outr)).
  solve_product.
Defined.

Lemma product_assoc' :
  forall (C : Cat) (hp : HasProducts C) (A B C : Ob C),
    {f : Hom (product (product A B) C) (product A (product B C)) | isIso f}.
Proof.
  intros.
  exists (fpair (outl .> outl) (fpair (outl .> outr) outr)),
         (fpair (fpair outl (outr .> outl)) (outr .> outr)).
  solve_product.
Defined.

Definition ProductFunctor_fmap
  {C : Cat} {hp : HasProducts C}
  {A B A' B' : Ob C} (f : Hom A A') (g : Hom B B')
  : Hom (product A B) (product A' B') :=
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
  solve_product.
Qed.

Lemma ProductFunctor_fmap_id :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C),
    ProductFunctor_fmap (id X) (id Y) == id (product X Y).
Proof.
  unfold ProductFunctor_fmap.
  solve_product.
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
  solve_product.
Defined.

Lemma ProductFunctor_fmap_comp_l :
  forall
    {C : Cat} {hp : HasProducts C}
    {X Y Z A : Ob C} (f : Hom X Y) (g : Hom Y Z),
      ProductFunctor_fmap (f .> g) (id A)
        ==
      ProductFunctor_fmap f (id A) .> ProductFunctor_fmap g (id A).
Proof.
  now intros; rewrite <- ProductFunctor_fmap_comp, comp_id_l.
Defined.

Lemma ProductFunctor_fmap_comp_r :
  forall
    {C : Cat} {hp : HasProducts C}
    {X Y Z A : Ob C} (f : Hom X Y) (g : Hom Y Z),
      ProductFunctor_fmap (id A) (f .> g)
        ==
      ProductFunctor_fmap (id A) f .> ProductFunctor_fmap (id A) g.
Proof.
  now intros; rewrite <- ProductFunctor_fmap_comp, comp_id_r.
Defined.

#[refine]
#[export]
Instance ProductFunctor {C : Cat} {hp : HasProducts C} : Functor (CAT_product C C) C :=
{
  fob := fun P : Ob (CAT_product C C) => product (fst P) (snd P);
  fmap := fun (X Y : Ob (CAT_product C C)) (f : Hom X Y) => ProductFunctor_fmap (fst f) (snd f)
}.
Proof.
  - now proper; apply Proper_ProductFunctor_fmap.
  - now intros; apply ProductFunctor_fmap_comp.
  - now intros; apply ProductFunctor_fmap_id.
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
  all: solve_product.
Defined.