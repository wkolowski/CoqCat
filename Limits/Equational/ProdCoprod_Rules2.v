From Cat Require Export Cat.

Set Implicit Arguments.

Class HasProducts (C : Cat) : Type :=
{
  prodOb : Ob C -> Ob C -> Ob C;
  proj1 : forall {A B : Ob C}, Hom (prodOb A B) A;
  proj2 : forall {A B : Ob C}, Hom (prodOb A B) B;
  fpair :
    forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (prodOb A B);
  Proper_fpair :>
    forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@fpair A B X);
(* reflection *)
  fpair_id :
    forall X Y : Ob C,
      fpair proj1 proj2 == id (prodOb X Y);
(* cancellation *)
  fpair_proj1 :
    forall (X Y A : Ob C) (f : Hom A X) (g : Hom A Y),
      fpair f g .> proj1 == f;
  fpair_proj2 :
    forall (X Y A : Ob C) (f : Hom A X) (g : Hom A Y),
      fpair f g .> proj2 == g;
(* fusion *)
  fpair_pre :
    forall (A B X Y : Ob C) (f : Hom A B) (g1 : Hom B X) (g2 : Hom B Y),
      fpair (f .> g1) (f .> g2) == f .> fpair g1 g2
}.

Arguments prodOb {C HasProducts} _ _.
Arguments proj1  {C HasProducts A B}.
Arguments proj2  {C HasProducts A B}.
Arguments fpair  {C HasProducts A B X} _ _.

Ltac prod := intros; try split;
repeat match goal with
| |- context [fpair (_ .> proj1) (_ .> proj2)] => rewrite fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite <- fpair_pre
| |- context [fpair _ _ .> proj1] => rewrite fpair_proj1
| |- context [fpair _ _ .> proj2] => rewrite fpair_proj2
| |- context [fpair proj1 proj2] => rewrite fpair_id
| |- ?x == ?x => reflexivity
| |- fpair _ _ == fpair _ _ => apply Proper_fpair
| |- context [id _ .> _] => rewrite id_left
| |- context [_ .> id _] => rewrite id_right
| |- fpair _ _ == id (prodOb _ _) => rewrite <- fpair_id; apply Proper_fpair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; auto
end.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : HasProducts C) (A X Y : Ob C) (f : Hom A (prodOb X Y)),
    fpair (f .> proj1) (f .> proj2) == f.
Proof. prod. Qed.

Lemma fpair_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A X Y X' Y' : Ob C) (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) == fpair f g .> fpair (proj1 .> h1) (proj2 .> h2).
Proof. prod. Qed.

Class HasCoproducts (C : Cat) : Type :=
{
  coprodOb : Ob C -> Ob C -> Ob C;
  coproj1 : forall {A B : Ob C}, Hom A (coprodOb A B);
  coproj2 : forall {A B : Ob C}, Hom B (coprodOb A B);
  copair :
    forall {A B X : Ob C} (f : Hom A X) (g : Hom B X), Hom (coprodOb A B) X;
  Proper_copair :>
    forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@copair A B X);
(* reflection *)
  copair_id :
    forall X Y : Ob C,
      copair coproj1 coproj2 == id (coprodOb X Y);
(* cancellation *)
  copair_coproj1 :
    forall (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
      coproj1 .> copair f g == f;
  copair_coproj2 :
    forall (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
      coproj2 .> copair f g == g;
(* fusion *)
  copair_post :
    forall (X Y A B : Ob C) (f1 : Hom X A) (f2 : Hom Y A) (g : Hom A B),
      copair (f1 .> g) (f2 .> g) == copair f1 f2 .> g
}.

Arguments coprodOb {C HasCoproducts} _ _.
Arguments coproj1  {C HasCoproducts A B}.
Arguments coproj2  {C HasCoproducts A B}.
Arguments copair   {C HasCoproducts A B X} _ _.

Ltac coprod := intros; try split;
repeat match goal with
| |- context [copair (coproj1 .> ?x) (coproj2 .> ?x)] => rewrite copair_post, copair_id
| |- context [copair _ _ .> _] => rewrite <- copair_post
| |- context [coproj1 .> copair _ _] => rewrite copair_coproj1
| |- context [coproj2 .> copair _ _] => rewrite copair_coproj2
| |- context [copair coproj1 coproj2] => rewrite copair_id
| |- ?x == ?x => reflexivity
| |- copair _ _ == copair _ _ => apply Proper_copair
| |- context [id _ .> _] => rewrite id_left
| |- context [_ .> id _] => rewrite id_right
| |- copair _ _ == id (coprodOb _ _) => rewrite <- copair_id; apply Proper_copair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite ?comp_assoc; auto
end.

Lemma copair_comp :
  forall
    (C : Cat) (hp : HasCoproducts C) (X Y X' Y' A : Ob C)
    (f : Hom X A) (g : Hom Y A) (h1 : Hom X' X) (h2 : Hom Y' Y),
      copair (h1 .> f) (h2 .> g) == copair (h1 .> coproj1) (h2 .> coproj2) .> copair f g.
Proof. coprod. Qed.

Class HasBiproducts (C : Cat) : Type :=
{
  products :> HasProducts C;
  coproducts :> HasCoproducts C;
  product_is_coproduct : forall X Y : Ob C, prodOb X Y = coprodOb X Y
}.

Coercion products : HasBiproducts >-> HasProducts.
Coercion coproducts : HasBiproducts >-> HasCoproducts.

(** * Duality *)

#[refine]
#[export]
Instance HasProducts_Dual {C : Cat} (hp : HasCoproducts C) : HasProducts (Dual C) :=
{
  prodOb := @coprodOb C hp;
  fpair := @copair C hp;
  proj1 := @coproj1 C hp;
  proj2 := @coproj2 C hp;
}.
Proof. all: cat; coprod. Defined.

#[refine]
#[export]
Instance HasCoproducts_Dual (C : Cat) (hp : HasProducts C) : HasCoproducts (Dual C) :=
{
  coprodOb := @prodOb C hp;
  copair := @fpair C hp;
  coproj1 := @proj1 C hp;
  coproj2 := @proj2 C hp;
}.
Proof. all: cat; prod. Defined.

#[refine]
#[export]
Instance HasBiproducts_Dual (C : Cat) (hb : HasBiproducts C) : HasBiproducts (Dual C) :=
{
  products := HasProducts_Dual (@coproducts C hb);
  coproducts := HasCoproducts_Dual (@products C hb);
}.
Proof.
  intros. destruct hb. cbn in *. rewrite product_is_coproduct0. reflexivity.
Defined.

(** * Equivalence of equational and traditional definitions *)

From Cat Require Limits.ProdCoprod.

Module Equiv.

#[refine]
#[export]
Instance hp_hpeq (C : Cat) (hp : ProdCoprod.HasProducts C) : HasProducts C :=
{
  prodOb := @ProdCoprod.prodOb C hp;
  proj1 := @ProdCoprod.proj1 C hp;
  proj2 := @ProdCoprod.proj2 C hp;
  fpair := @ProdCoprod.fpair C hp;
}.
Proof. all: ProdCoprod.fpair. Defined.

#[refine]
#[export]
Instance hpeq_hp (C : Cat) (hp_eq : HasProducts C) : ProdCoprod.HasProducts C :=
{
  prodOb := @prodOb C hp_eq;
  proj1 := @proj1 C hp_eq;
  proj2 := @proj2 C hp_eq;
  fpair := @fpair C hp_eq;
}.
Proof.
  unfold ProdCoprod.product, setoid_unique. cat.
    rewrite fpair_proj1. reflexivity.
    rewrite fpair_proj2. reflexivity.
    rewrite H, H0. rewrite fpair_pre, fpair_id, id_right. reflexivity.
Defined.

#[refine]
#[export]
Instance hp_hpeq' (C : Cat) (hp : ProdCoprod.HasCoproducts C) : HasCoproducts C :=
{
  coprodOb := @ProdCoprod.coprodOb C hp;
  coproj1 := @ProdCoprod.coproj1 C hp;
  coproj2 := @ProdCoprod.coproj2 C hp;
  copair := @ProdCoprod.copair C hp;
}.
Proof. all: ProdCoprod.copair. Defined.

#[refine]
#[export]
Instance hpeq_hp' (C : Cat) (hp_eq : HasCoproducts C) : ProdCoprod.HasCoproducts C :=
{
  coprodOb := @coprodOb C hp_eq;
  coproj1 := @coproj1 C hp_eq;
  coproj2 := @coproj2 C hp_eq;
  copair := @copair C hp_eq;
}.
Proof.
  unfold ProdCoprod.coproduct, setoid_unique. cat.
    rewrite copair_coproj1. reflexivity.
    rewrite copair_coproj2. reflexivity.
    rewrite H, H0. rewrite copair_post, copair_id, id_left. reflexivity.
Defined.

#[refine]
#[export]
Instance hb_hbeq (C : Cat) (hb : ProdCoprod.HasBiproducts C) : HasBiproducts C :=
{
  products := @hp_hpeq C (@ProdCoprod.products C hb);
  coproducts := @hp_hpeq' C (@ProdCoprod.coproducts C hb);
}.
Proof.
  intros. destruct hb. cbn. apply product_is_coproduct0.
Defined.

#[refine]
#[export]
Instance hbeq_hb (C : Cat) (hb : HasBiproducts C) : ProdCoprod.HasBiproducts C :=
{
  ProdCoprod.products := @hpeq_hp C (@products C hb);
  ProdCoprod.coproducts := @hpeq_hp' C (@coproducts C hb);
}.
Proof.
  intros. destruct hb. cbn. apply product_is_coproduct0.
Defined.

End Equiv.

(** * Lemmas ported from ProdCoprod.v *)

(*
Lemma iso_to_prod :
  forall
    (C : Cat) (X Y : Ob C)
    (P Q : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (fpair : forall Q : Ob C, Hom Q X -> Hom Q Y -> Hom Q P),
      product C P p1 p2 fpair ->
      forall (f : Hom Q P) (H : Iso f),
      product C Q (f .> p1) (f .> p2)
        (fun (A : Ob C) (p1' : Hom A X) (p2' : Hom A Y) =>
          match constructive_indefinite_description _ H with
          | exist _ g _ => fpair A p1' p2' .> g
          end).
*)

Lemma prodOb_comm :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C),
    prodOb X Y ~ prodOb Y X.
Proof.
  intros.
  red. exists (fpair proj2 proj1).
  red. exists (fpair proj2 proj1).
  prod.
Qed.

Lemma prodOb_assoc :
  forall (C : Cat) (hp : HasProducts C) (X Y Z : Ob C),
    prodOb X (prodOb Y Z) ~ prodOb (prodOb X Y) Z.
Proof.
  intros.
  red. exists (fpair (fpair proj1 (proj2 .> proj1)) (proj2 .> proj2)).
  red. exists (fpair (proj1 .> proj1) (fpair (proj1 .> proj2) proj2)).
  prod.
Qed.

Lemma prodOb_assoc' :
  forall (C : Cat) (hp : HasProducts C) (X Y Z : Ob C),
    {f : Hom (prodOb (prodOb X Y) Z) (prodOb X (prodOb Y Z)) | Iso f}.
Proof.
  intros.
  exists (fpair (proj1 .> proj1) (fpair (proj1 .> proj2) proj2)).
  red. exists (fpair (fpair proj1 (proj2 .> proj1)) (proj2 .> proj2)).
  prod.
Defined.

(*
Lemma coproduct_uiso :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A)
    (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q)
    (copair' : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom Q A),
      coproduct C P p1 p2 copair -> coproduct C Q q1 q2 copair' ->
        exists !! f : Hom P Q, Iso f /\ p1 .> f == q1 /\ p2 .> f == q2.

Lemma coproduct_copair_equiv :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A)
    (copair' : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      coproduct C P p1 p2 copair -> coproduct C P p1 p2 copair' ->
        forall (A : Ob C) (f : Hom X A) (g : Hom Y A), copair A f g == copair' A f g.
Proof.
  intros. edestruct H, H0. apply H2. cat.
Qed.
*)

Lemma coprodOb_comm :
  forall (C : Cat) (hp : HasCoproducts C) (X Y : Ob C),
    coprodOb X Y ~ coprodOb Y X.
Proof.
  intros.
  red. exists (copair coproj2 coproj1).
  red. exists (copair coproj2 coproj1).
  coprod.
Qed.

Lemma coprodOb_assoc :
  forall (C : Cat) (hp : HasCoproducts C) (X Y Z : Ob C),
    coprodOb X (coprodOb Y Z) ~ coprodOb (coprodOb X Y) Z.
Proof.
  intros.
  red. exists (copair (coproj1 .> coproj1) (copair (coproj2 .> coproj1) coproj2)).
  red. exists (copair (copair coproj1 (coproj1 .> coproj2)) (coproj2 .> coproj2)).
  coprod.
Qed.

Lemma coprodOb_assoc' :
  forall (C : Cat) (hp : HasCoproducts C) (X Y Z : Ob C),
    {f : Hom (coprodOb (coprodOb X Y) Z) (coprodOb X (coprodOb Y Z)) | Iso f}.
Proof.
  intros.
  exists (copair (copair coproj1 (coproj1 .> coproj2)) (coproj2 .> coproj2)).
  red. exists (copair (coproj1 .> coproj1) (copair (coproj2 .> coproj1) coproj2)).
  coprod.
Defined.

(** * Product and coproduct functors *)

Definition ProductFunctor_fmap
  {C : Cat} {hp : HasProducts C} {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
  : Hom (prodOb X X') (prodOb Y Y')
  := fpair (proj1 .> f) (proj2 .> g).

#[export]
Instance Proper_ProductFunctor_fmap :
  forall (C : Cat) (hp : HasProducts C) (X X' Y Y' : Ob C),
    Proper
      ((@equiv _ (HomSetoid X Y))  ==>
      (@equiv _ (HomSetoid X' Y'))  ==>
      (@equiv _ (HomSetoid (prodOb X X') (prodOb Y Y'))))
      (@ProductFunctor_fmap C hp X X' Y Y').
Proof.
  unfold Proper, respectful, ProductFunctor_fmap. intros.
  rewrite H, H0. reflexivity.
Qed.

Lemma ProductFunctor_fmap_pres_id :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C),
    ProductFunctor_fmap (id X) (id Y) == id (prodOb X Y).
Proof.
  intros; unfold ProductFunctor_fmap. prod.
Defined.

Lemma ProductFunctor_fmap_pres_comp :
  forall
    (C : Cat) (hp : HasProducts C) (A1 A2 B1 B2 C1 C2 : Ob C)
    (f1 : Hom A1 B1) (g1 : Hom B1 C1) (f2 : Hom A2 B2) (g2 : Hom B2 C2),
      ProductFunctor_fmap (f1 .> g1) (f2 .> g2)
        ==
      ProductFunctor_fmap f1 f2 .> ProductFunctor_fmap g1 g2.
Proof.
  unfold ProductFunctor_fmap. prod.
Defined.

Lemma ProductFunctor_fmap_pres_comp_l :
  forall
    {C : Cat} {hp : HasProducts C}
    {X Y : Ob C} (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
      ProductFunctor_fmap (f .> g) (id Z)
        ==
      ProductFunctor_fmap f (id Z) .> ProductFunctor_fmap g (id Z).
Proof.
  intros. rewrite <- ProductFunctor_fmap_pres_comp. cat.
Defined.

Lemma ProductFunctor_fmap_pres_comp_r :
  forall
    {C : Cat} {hp : HasProducts C}
    {X Y : Ob C} (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
      ProductFunctor_fmap (id Z) (f .> g)
        ==
      ProductFunctor_fmap (id Z) f .> ProductFunctor_fmap (id Z) g.
Proof.
  intros. rewrite <- ProductFunctor_fmap_pres_comp. cat.
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
  intros. apply ProductFunctor_fmap_pres_comp.
  intros. apply ProductFunctor_fmap_pres_id.
Defined.

Notation "A × B" := (fob ProductFunctor (A, B)) (at level 40).
Notation "f ×' g" := (ProductFunctor_fmap f g) (at level 40).

Definition CoproductFunctor_fmap
  {C : Cat} {hp : HasCoproducts C} {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
  : Hom (coprodOb X X') (coprodOb Y Y')
  := copair (f .> coproj1) (g .> coproj2).

#[export]
Instance Proper_CoproductFunctor_fmap :
  forall (C : Cat) (hp : HasCoproducts C) (X X' Y Y' : Ob C),
    Proper
      ((@equiv _ (HomSetoid X Y))  ==>
      (@equiv _ (HomSetoid X' Y'))  ==>
      (@equiv _ (HomSetoid (coprodOb X X') (coprodOb Y Y'))))
      (@CoproductFunctor_fmap C hp X X' Y Y').
Proof.
  unfold Proper, respectful, CoproductFunctor_fmap. coprod.
Qed.

Lemma CoproductFunctor_fmap_pres_id :
  forall (C : Cat) (hp : HasCoproducts C) (X Y : Ob C),
    CoproductFunctor_fmap (id X) (id Y) == id (coprodOb X Y).
Proof.
  intros; unfold CoproductFunctor_fmap. coprod.
Defined.

Lemma CoproductFunctor_fmap_pres_comp :
  forall
    (C : Cat) (hp : HasCoproducts C) (A1 A2 B1 B2 C1 C2 : Ob C)
    (f1 : Hom A1 B1) (g1 : Hom B1 C1) (f2 : Hom A2 B2) (g2 : Hom B2 C2),
      CoproductFunctor_fmap (f1 .> g1) (f2 .> g2)
        ==
      CoproductFunctor_fmap f1 f2 .> CoproductFunctor_fmap g1 g2.
Proof.
  unfold CoproductFunctor_fmap; intros. coprod.
Defined.

Lemma CoproductFunctor_fmap_pres_comp_l :
  forall
    {C : Cat} {hp : HasCoproducts C}
    {X Y : Ob C} (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
      CoproductFunctor_fmap (f .> g) (id Z)
        ==
      CoproductFunctor_fmap f (id Z) .> CoproductFunctor_fmap g (id Z).
Proof.
  intros. rewrite <- CoproductFunctor_fmap_pres_comp. cat.
Defined.

Lemma CoproductFunctor_fmap_pres_comp_r :
  forall
    {C : Cat} {hp : HasCoproducts C}
    {X Y : Ob C} (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
      CoproductFunctor_fmap (id Z) (f .> g)
        ==
      CoproductFunctor_fmap (id Z) f .> CoproductFunctor_fmap (id Z) g.
Proof.
  intros. rewrite <- CoproductFunctor_fmap_pres_comp. cat.
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
  intros. apply CoproductFunctor_fmap_pres_comp.
  intros. apply CoproductFunctor_fmap_pres_id.
Defined.

Notation "A + B" := (fob CoproductFunctor (A, B)).
Notation "f +' g" := (CoproductFunctor_fmap f g) (at level 40).