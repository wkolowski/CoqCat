Require Export Cat.
Require Export Cat.Functor.

Set Implicit Arguments.

Class has_products (C : Cat) : Type :=
{
    prodOb : Ob C -> Ob C -> Ob C;
    proj1 : forall {A B : Ob C}, Hom (prodOb A B) A;
    proj2 : forall {A B : Ob C}, Hom (prodOb A B) B;
    fpair :
      forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (prodOb A B);
    fpair_Proper :>
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

Ltac prod := intros; try split;
repeat match goal with
    | |- context [fpair (_ .> proj1) (_ .> proj2)] =>
        rewrite fpair_pre, fpair_id
    | |- context [_ .> fpair _ _] => rewrite <- fpair_pre
    | |- context [fpair _ _ .> proj1] => rewrite fpair_proj1
    | |- context [fpair _ _ .> proj2] => rewrite fpair_proj2
    | |- context [fpair proj1 proj2] => rewrite fpair_id
    | |- ?x == ?x => reflexivity
    | |- fpair _ _ == fpair _ _ => apply fpair_Proper
    | |- context [id _ .> _] => rewrite id_left
    | |- context [_ .> id _] => rewrite id_right
    | |- fpair _ _ == id (prodOb _ _) =>
        rewrite <- fpair_id; apply fpair_Proper
    | |- ?f .> ?g == ?f .> ?g' => f_equiv
    | |- ?f .> ?g == ?f' .> ?g => f_equiv
    | _ => rewrite <- ?comp_assoc; auto
end.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : has_products C) (A X Y : Ob C)
  (f : Hom A (prodOb X Y)),
    fpair (f .> proj1) (f .> proj2) == f.
Proof. prod. Qed.

Lemma fpair_comp :
  forall
    (C : Cat) (hp : has_products C)
    (A X Y X' Y' : Ob C)
    (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) ==
      fpair f g .> fpair (proj1 .> h1) (proj2 .> h2).
Proof. prod. Qed.

Class has_coproducts (C : Cat) : Type :=
{
    coprodOb : Ob C -> Ob C -> Ob C;
    coproj1 : forall {A B : Ob C}, Hom A (coprodOb A B);
    coproj2 : forall {A B : Ob C}, Hom B (coprodOb A B);
    copair :
      forall {A B X : Ob C} (f : Hom A X) (g : Hom B X), Hom (coprodOb A B) X;
    copair_Proper :>
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

Ltac coprod := intros; try split;
repeat match goal with
    | |- context [copair (coproj1 .> ?x) (coproj2 .> ?x)] =>
        rewrite copair_post, copair_id
    | |- context [copair _ _ .> _] => rewrite <- copair_post
    | |- context [coproj1 .> copair _ _] => rewrite copair_coproj1
    | |- context [coproj2 .> copair _ _] => rewrite copair_coproj2
    | |- context [copair coproj1 coproj2] => rewrite copair_id
    | |- ?x == ?x => reflexivity
    | |- copair _ _ == copair _ _ => apply copair_Proper
    | |- context [id _ .> _] => rewrite id_left
    | |- context [_ .> id _] => rewrite id_right
    | |- copair _ _ == id (coprodOb _ _) =>
        rewrite <- copair_id; apply copair_Proper
    | |- ?f .> ?g == ?f .> ?g' => f_equiv
    | |- ?f .> ?g == ?f' .> ?g => f_equiv
    | _ => rewrite ?comp_assoc; auto
end.

Lemma copair_comp : 
  forall (C : Cat) (hp : has_coproducts C) (X Y X' Y' A : Ob C)
    (f : Hom X A) (g : Hom Y A) (h1 : Hom X' X) (h2 : Hom Y' Y),
      copair (h1 .> f) (h2 .> g) ==
      copair (h1 .> coproj1) (h2 .> coproj2) .> copair f g.
Proof. coprod. Qed.

Class has_biproducts (C : Cat) : Type :=
{
    products :> has_products C;
    coproducts :> has_coproducts C;
    product_is_coproduct :
      forall X Y : Ob C, prodOb X Y = coprodOb X Y
}.

Coercion products : has_biproducts >-> has_products.
Coercion coproducts : has_biproducts >-> has_coproducts.

(* Equivalence to the old definition *)

Module Equiv.

Require BinProdCoprod.

#[refine]
Instance hp_hpeq
  (C : Cat) (hp : BinProdCoprod.has_products C) : has_products C :=
{
    prodOb := @BinProdCoprod.prodOb C hp;
    proj1 := @BinProdCoprod.proj1 C hp;
    proj2 := @BinProdCoprod.proj2 C hp;
    fpair := @BinProdCoprod.fpair C hp;
}.
Proof. all: BinProdCoprod.fpair. Defined.

#[refine]
Instance hpeq_hp
  (C : Cat) (hp_eq : has_products C) : BinProdCoprod.has_products C :=
{
    prodOb := @prodOb C hp_eq;
    proj1 := @proj1 C hp_eq;
    proj2 := @proj2 C hp_eq;
    fpair := @fpair C hp_eq;
}.
Proof.
  unfold BinProdCoprod.product_skolem, setoid_unique. cat.
    rewrite fpair_proj1. reflexivity.
    rewrite fpair_proj2. reflexivity.
    rewrite H, H0. rewrite fpair_pre, fpair_id, id_right. reflexivity.
Defined.

#[refine]
Instance hp_hpeq'
  (C : Cat) (hp : BinProdCoprod.has_coproducts C) : has_coproducts C :=
{
    coprodOb := @BinProdCoprod.coprodOb C hp;
    coproj1 := @BinProdCoprod.coproj1 C hp;
    coproj2 := @BinProdCoprod.coproj2 C hp;
    copair := @BinProdCoprod.copair C hp;
}.
Proof. all: BinProdCoprod.copair. Defined.

#[refine]
Instance hpeq_hp'
  (C : Cat) (hp_eq : has_coproducts C) : BinProdCoprod.has_coproducts C :=
{
    coprodOb := @coprodOb C hp_eq;
    coproj1 := @coproj1 C hp_eq;
    coproj2 := @coproj2 C hp_eq;
    copair := @copair C hp_eq;
}.
Proof.
  unfold BinProdCoprod.coproduct_skolem, setoid_unique. cat.
    rewrite copair_coproj1. reflexivity.
    rewrite copair_coproj2. reflexivity.
    rewrite H, H0. rewrite copair_post, copair_id, id_left. reflexivity.
Defined.

#[refine]
Instance hb_hbeq
  (C : Cat) (hb : BinProdCoprod.has_biproducts C) : has_biproducts C :=
{
    products := @hp_hpeq C (@BinProdCoprod.products C hb);
    coproducts := @hp_hpeq' C (@BinProdCoprod.coproducts C hb);
}.
Proof.
  intros. destruct hb. cbn. apply product_is_coproduct0.
Defined.

#[refine]
Instance hbeq_hb
  (C : Cat) (hb : has_biproducts C) : BinProdCoprod.has_biproducts C :=
{
    BinProdCoprod.products := @hpeq_hp C (@products C hb);
    BinProdCoprod.coproducts := @hpeq_hp' C (@coproducts C hb);
}.
Proof.
  intros. destruct hb. cbn. apply product_is_coproduct0.
Defined.

End Equiv.

(* Lemmas ported from BinProdCoprod.v *)

#[refine]
Instance Dual_prod_coprod
  (C : Cat) (hp : has_products C) : has_coproducts (Dual C) :=
{
    coprodOb := @prodOb C hp;
    copair := @fpair C hp;
    coproj1 := @proj1 C hp;
    coproj2 := @proj2 C hp;
}.
Proof. all: cat; prod. Defined.

#[refine]
Instance Dual_coprod_prod
  {C : Cat} (hp : has_coproducts C) : has_products (Dual C) :=
{
    prodOb := @coprodOb C hp;
    fpair := @copair C hp;
    proj1 := @coproj1 C hp;
    proj2 := @coproj2 C hp;
}.
Proof. all: cat; coprod. Defined.

#[refine]
Instance Dual_biprod
  (C : Cat) (hb : has_biproducts C) : has_biproducts (Dual C) :=
{
    products := Dual_coprod_prod (@coproducts C hb);
    coproducts := Dual_prod_coprod (@products C hb);
}.
Proof.
  intros. destruct hb. cbn in *. rewrite product_is_coproduct0. reflexivity.
Defined.

(*
Lemma has_products_equiv :
  forall
    (C : Cat) (hp hp' : has_products C),
(*      @prodOb C hp = @prodOb C hp' /\*)
      @proj1 C hp == @proj1 C hp'. /\
      @proj2 C hp == @proj2 C hp' /\
      @fpair C hp == @fpair C hp'.
*)

(*
Lemma iso_to_prod_skolem :
  forall (C : Cat) (X Y : Ob C)
  (P Q : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (fpair : forall Q : Ob C, Hom Q X -> Hom Q Y -> Hom Q P),
    product_skolem C P p1 p2 fpair ->
    forall (f : Hom Q P) (H : Iso f),
    product_skolem C Q (f .> p1) (f .> p2)
      (fun (A : Ob C) (p1' : Hom A X) (p2' : Hom A Y) =>
        match constructive_indefinite_description _ H with
          | exist _ g _ => fpair A p1' p2' .> g
        end).
*)

Lemma prodOb_comm :
  forall (C : Cat) (hp : has_products C) (X Y : Ob C),
    prodOb X Y ~ prodOb Y X.
Proof.
  intros.
  red. exists (fpair proj2 proj1).
  red. exists (fpair proj2 proj1).
  prod.
Qed.

Lemma prodOb_assoc :
  forall (C : Cat) (hp : has_products C) (X Y Z : Ob C),
    prodOb X (prodOb Y Z) ~ prodOb (prodOb X Y) Z.
Proof.
  intros.
  red. exists (fpair (fpair proj1 (proj2 .> proj1)) (proj2 .> proj2)).
  red. exists (fpair (proj1 .> proj1) (fpair (proj1 .> proj2) proj2)).
  prod.
Qed.

Lemma prodOb_assoc' :
  forall (C : Cat) (hp : has_products C) (X Y Z : Ob C),
    {f : Hom (prodOb (prodOb X Y) Z) (prodOb X (prodOb Y Z)) | Iso f}.
Proof.
  intros.
  exists (fpair (proj1 .> proj1) (fpair (proj1 .> proj2) proj2)).
  red. exists (fpair (fpair proj1 (proj2 .> proj1)) (proj2 .> proj2)).
  Time prod.
Defined.

(*
Lemma coproduct_skolem_uiso :
  forall (C : Cat) (X Y : Ob C)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A)
  (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q)
  (copair' : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom Q A),
    coproduct_skolem C P p1 p2 copair ->
    coproduct_skolem C Q q1 q2 copair' ->
    exists !! f : Hom P Q, Iso f /\
      p1 .> f == q1 /\
      p2 .> f == q2.

Lemma coproduct_skolem_copair_equiv :
  forall (C : Cat) (X Y : Ob C)
  (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
  (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A)
  (copair' : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
    coproduct_skolem C P p1 p2 copair ->
    coproduct_skolem C P p1 p2 copair' ->
      forall (A : Ob C) (f : Hom X A) (g : Hom Y A),
        copair A f g == copair' A f g.
Proof.
  intros. edestruct H, H0. apply H2. cat.
Qed.
*)

Lemma coprodOb_comm :
  forall (C : Cat) (hp : has_coproducts C) (X Y : Ob C),
    coprodOb X Y ~ coprodOb Y X.
Proof.
  intros.
  red. exists (copair coproj2 coproj1).
  red. exists (copair coproj2 coproj1).
  coprod.
Qed.

Lemma coprodOb_assoc :
  forall (C : Cat) (hp : has_coproducts C) (X Y Z : Ob C),
    coprodOb X (coprodOb Y Z) ~ coprodOb (coprodOb X Y) Z.
Proof.
  intros.
  red. exists (copair (coproj1 .> coproj1) (copair (coproj2 .> coproj1) coproj2)).
  red. exists (copair (copair coproj1 (coproj1 .> coproj2)) (coproj2 .> coproj2)).
  coprod.
Qed.

Lemma coprodOb_assoc' :
  forall (C : Cat) (hp : has_coproducts C) (X Y Z : Ob C),
    {f : Hom (coprodOb (coprodOb X Y) Z) (coprodOb X (coprodOb Y Z)) | Iso f}.
Proof.
  intros.
  exists (copair (copair coproj1 (coproj1 .> coproj2)) (coproj2 .> coproj2)).
  red. exists (copair (coproj1 .> coproj1) (copair (coproj2 .> coproj1) coproj2)).
  coprod.
Defined.

Definition ProdCatHom {C D : Cat} (X Y : Ob C * Ob D) :=
  prod (Hom (fst X) (fst Y)) (Hom (snd X) (snd Y)).

#[refine]
Instance ProdCatSetoid {C D : Cat} (X Y : Ob C * Ob D)
    : Setoid (ProdCatHom X Y) :=
{
  equiv := fun f g : ProdCatHom X Y =>
    @equiv (@Hom C (fst X) (fst Y)) (@HomSetoid C (fst X) (fst Y))
    (fst f) (fst g) /\
    @equiv (@Hom D (snd X) (snd Y)) (@HomSetoid D (snd X) (snd Y))
    (snd f) (snd g)
}.
Proof.
  split; red; intros; split; try destruct H; try destruct H0;
  try rewrite H; try rewrite H1; try rewrite H0; auto; reflexivity. 
Defined.

#[refine]
Instance CAT_prodOb (C : Cat) (D : Cat) : Cat :=
{
    Ob := Ob C * Ob D;
    Hom := ProdCatHom;
    HomSetoid := ProdCatSetoid;
    comp := fun (X Y Z : Ob C * Ob D)
        (f : Hom (fst X) (fst Y) * Hom (snd X) (snd Y))
        (g : Hom (fst Y) (fst Z) * Hom (snd Y) (snd Z)) =>
        (fst f .> fst g, snd f .> snd g);
    id := fun A : Ob C * Ob D => (id (fst A), id (snd A))
}.
Proof.
  (* Proper *) proper; my_simpl.
    rewrite H, H0. reflexivity.
    rewrite H1, H2. reflexivity.
  (* Category laws *) all: cat.
Defined.

Definition ProductFunctor_fmap {C : Cat} {hp : has_products C}
    {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
    : Hom (prodOb X X') (prodOb Y Y') :=
      fpair (proj1 .> f) (proj2 .> g).

Instance ProductFunctor_fmap_Proper : forall (C : Cat)
    (hp : has_products C) (X X' Y Y' : Ob C),
    Proper ((@equiv _ (HomSetoid X Y))  ==>
      (@equiv _ (HomSetoid X' Y'))  ==>
      (@equiv _ (HomSetoid (prodOb X X') (prodOb Y Y'))))
      (@ProductFunctor_fmap C hp X X' Y Y').
Proof.
  unfold Proper, respectful, ProductFunctor_fmap. intros.
  rewrite H, H0. reflexivity.
Qed.

Lemma ProductFunctor_fmap_pres_id : forall (C : Cat)
    (hp : has_products C) (X Y : Ob C),
    ProductFunctor_fmap (id X) (id Y) == id (prodOb X Y).
Proof.
  intros; unfold ProductFunctor_fmap. prod.
Defined.

Lemma ProductFunctor_fmap_pres_comp : forall (C : Cat)
    (hp : has_products C) (A1 A2 B1 B2 C1 C2 : Ob C)
    (f1 : Hom A1 B1) (g1 : Hom B1 C1) (f2 : Hom A2 B2) (g2 : Hom B2 C2),
    ProductFunctor_fmap (f1 .> g1) (f2 .> g2) ==
    ProductFunctor_fmap f1 f2 .> ProductFunctor_fmap g1 g2.
Proof.
  unfold ProductFunctor_fmap. prod.
Defined.

Lemma ProductFunctor_fmap_pres_comp_l :
    forall {C : Cat} {hp : has_products C} {X Y : Ob C}
    (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
    ProductFunctor_fmap (f .> g) (id Z) == 
    ProductFunctor_fmap f (id Z) .> ProductFunctor_fmap g (id Z).
Proof.
  intros. rewrite <- ProductFunctor_fmap_pres_comp. cat.
Defined.

Lemma ProductFunctor_fmap_pres_comp_r :
    forall {C : Cat} {hp : has_products C} {X Y : Ob C}
    (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
    ProductFunctor_fmap (id Z) (f .> g) ==
    ProductFunctor_fmap (id Z) f .> ProductFunctor_fmap (id Z) g.
Proof.
  intros. rewrite <- ProductFunctor_fmap_pres_comp. cat.
Defined.

#[refine]
Instance ProductFunctor {C : Cat} {hp : has_products C} :
    Functor (CAT_prodOb C C) C :=
{
    fob := fun P : Ob (CAT_prodOb C C) => prodOb (fst P) (snd P);
    fmap := fun (X Y : Ob (CAT_prodOb C C)) (f : Hom X Y) =>
      ProductFunctor_fmap (fst f) (snd f)
}.
Proof.
  proper. apply ProductFunctor_fmap_Proper; cat.
  intros. apply ProductFunctor_fmap_pres_comp.
  intros. apply ProductFunctor_fmap_pres_id.
Defined.

Definition CoproductFunctor_fmap {C : Cat} {hp : has_coproducts C}
    {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
      : Hom (coprodOb X X') (coprodOb Y Y') :=
      (copair (f .> coproj1) (g .> coproj2)).

Instance CoproductFunctor_fmap_Proper : forall (C : Cat)
    (hp : has_coproducts C) (X X' Y Y' : Ob C),
    Proper ((@equiv _ (HomSetoid X Y))  ==>
      (@equiv _ (HomSetoid X' Y'))  ==>
      (@equiv _ (HomSetoid (coprodOb X X') (coprodOb Y Y'))))
      (@CoproductFunctor_fmap C hp X X' Y Y').
Proof.
  unfold Proper, respectful, CoproductFunctor_fmap. coprod.
Qed.

Lemma CoproductFunctor_fmap_pres_id : forall (C : Cat)
    (hp : has_coproducts C) (X Y : Ob C),
    CoproductFunctor_fmap (id X) (id Y) == id (coprodOb X Y).
Proof.
  intros; unfold CoproductFunctor_fmap. coprod.
Defined.

Lemma CoproductFunctor_fmap_pres_comp : forall (C : Cat)
    (hp : has_coproducts C) (A1 A2 B1 B2 C1 C2 : Ob C)
    (f1 : Hom A1 B1) (g1 : Hom B1 C1) (f2 : Hom A2 B2) (g2 : Hom B2 C2),
    CoproductFunctor_fmap (f1 .> g1) (f2 .> g2) ==
    CoproductFunctor_fmap f1 f2 .> CoproductFunctor_fmap g1 g2.
Proof.
  unfold CoproductFunctor_fmap; intros. coprod.
Defined.

Lemma CoproductFunctor_fmap_pres_comp_l :
    forall {C : Cat} {hp : has_coproducts C} {X Y : Ob C}
    (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
    CoproductFunctor_fmap (f .> g) (id Z) == 
    CoproductFunctor_fmap f (id Z) .> CoproductFunctor_fmap g (id Z).
Proof.
  intros. rewrite <- CoproductFunctor_fmap_pres_comp. cat.
Defined.

Lemma CoproductFunctor_fmap_pres_comp_r :
    forall {C : Cat} {hp : has_coproducts C} {X Y : Ob C}
    (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
    CoproductFunctor_fmap (id Z) (f .> g) ==
    CoproductFunctor_fmap (id Z) f .> CoproductFunctor_fmap (id Z) g.
Proof.
  intros. rewrite <- CoproductFunctor_fmap_pres_comp. cat.
Defined.

#[refine]
Instance CoproductFunctor {C : Cat} (hp : has_coproducts C) :
    Functor (CAT_prodOb C C) C :=
{
    fob := fun P : Ob (CAT_prodOb C C) => coprodOb (fst P) (snd P);
    fmap := fun (X Y : Ob (CAT_prodOb C C)) (f : Hom X Y) =>
      CoproductFunctor_fmap (fst f) (snd f)
}.
Proof.
  proper. apply CoproductFunctor_fmap_Proper; cat.
  intros. apply CoproductFunctor_fmap_pres_comp.
  intros. apply CoproductFunctor_fmap_pres_id.
Defined.

Notation "A × B" := (fob ProductFunctor (A, B)) (at level 40).
Notation "f ×' g" := (ProductFunctor_fmap f g) (at level 40).
Notation "A + B" := (fob CoproductFunctor (A, B)).
Notation "f +' g" := (CoproductFunctor_fmap f g) (at level 40).