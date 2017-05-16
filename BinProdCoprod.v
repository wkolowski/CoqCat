Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.Cat.
Require Export Functor.

Definition product_skolem (C : Cat) {A B : Ob C}
    (P : Ob C) (p1 : Hom P A) (p2 : Hom P B)
    (fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P) : Prop :=
    forall (X : Ob C) (f : Hom X A) (g : Hom X B),
    setoid_unique (fun u : Hom X P => f == u .> p1 /\ g == u .> p2) (fpair f g).

Definition coproduct_skolem (C : Cat) {A B : Ob C} (P : Ob C)
    (p1 : Hom A P) (p2 : Hom B P)
    (copair : forall {X : Ob C} (f : Hom A X) (g : Hom B X), Hom P X) : Prop :=
    forall (X : Ob C) (f : Hom A X) (g : Hom B X),
    setoid_unique (fun d : Hom P X => f == p1 .> d /\ g == p2 .> d) (copair f g).

Definition biproduct_skolem (C : Cat) {A B : Ob C} (P : Ob C)
    (pA : Hom P A) (pB : Hom P B) (iA : Hom A P) (iB : Hom B P)
    (fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P)
    (copair : forall {X : Ob C} (f : Hom A X) (g : Hom B X), Hom P X) : Prop :=
    product_skolem C P pA pB (@fpair) /\ coproduct_skolem C P iA iB (@copair).

Class has_products (C : Cat) : Type :=
{
    prodOb : Ob C -> Ob C -> Ob C;
    proj1 : forall A B : Ob C, Hom (prodOb A B) A;
    proj2 : forall A B : Ob C, Hom (prodOb A B) B;
    fpair : forall {A B X : Ob C} (f : Hom X A) (g : Hom X B),
      Hom X (prodOb A B);
    fpair_Proper : forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@fpair A B X);
    is_product : forall (A B : Ob C),
      product_skolem C (prodOb A B) (proj1 A B) (proj2 A B) (@fpair A B)
}.

Arguments prodOb [C] [has_products] _ _.
Arguments proj1 [C] [has_products] [A] [B].
Arguments proj2 [C] [has_products] [A] [B].
Arguments fpair [C] [has_products] [A] [B] [X] _ _.

Class has_coproducts (C : Cat) : Type := 
{
    coprodOb : Ob C -> Ob C -> Ob C;
    coproj1 : forall A B : Ob C, Hom A (coprodOb A B);
    coproj2 : forall A B : Ob C, Hom B (coprodOb A B);
    copair : forall {A B X : Ob C} (f : Hom A X) (g : Hom B X),
      Hom (coprodOb A B) X;
    copair_Proper : forall (A B X : Ob C),
      Proper (equiv ==> equiv ==> equiv) (@copair A B X);
    is_coproduct : forall A B : Ob C,
      coproduct_skolem C (coprodOb A B) (coproj1 A B) (coproj2 A B) (@copair A B)
}.

Arguments coprodOb [C] [has_coproducts] _ _.
Arguments coproj1 [C] [has_coproducts] [A] [B].
Arguments coproj2 [C] [has_coproducts] [A] [B].
Arguments copair [C] [has_coproducts] [A] [B] [X] _ _.

Class has_biproducts (C : Cat) : Type :=
{
    products :> has_products C;
    coproducts :> has_coproducts C;
    product_is_coproduct : forall X Y : Ob C,
      prodOb X Y = coprodOb X Y
}.

Coercion products : has_biproducts >-> has_products.
Coercion coproducts : has_biproducts >-> has_coproducts.

Theorem dual_product_coproduct_skolem :
  forall (C : Cat) (X Y : Ob C)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (fpair : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P),
    product_skolem C P p1 p2 fpair <->
    coproduct_skolem (Dual C) P p1 p2 fpair.
Proof.
  cat.
Defined.

Theorem dual_biproduct_skolem_self :
  forall (C : Cat) (X Y : Ob C)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y) (q1 : Hom X P) (q2 : Hom Y P)
  (fpair : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P)
  (copair : forall (P' : Ob C) (q1' : Hom X P') (q2' : Hom Y P'), Hom P P'),
    biproduct_skolem C P p1 p2 q1 q2 fpair copair <->
    biproduct_skolem (Dual C) P q1 q2 p1 p2 copair fpair.
Proof.
  unfold biproduct_skolem. cat.
Qed.

Theorem fpair_proj1 : forall (C : Cat) (hp : has_products C) (X Y A : Ob C)
    (f : Hom A X) (g : Hom A Y), fpair f g .> proj1 == f.
Proof.
  destruct hp; simpl; intros. do 2 red in is_product0.
  destruct (is_product0 X Y A f g) as [[H1 H2] H3].
  rewrite <- H1. reflexivity.
Qed.

Theorem fpair_proj2 : forall (C : Cat) (hp : has_products C) (X Y A : Ob C)
    (f : Hom A X) (g : Hom A Y), fpair f g .> proj2 == g.
Proof.
  destruct hp; simpl; intros. do 2 red in is_product0.
  destruct (is_product0 X Y A f g) as [[H1 H2] H3].
  rewrite <- H2. reflexivity.
Qed.

Theorem fpair_pre : forall (C : Cat) (hp : has_products C) (A B X Y : Ob C)
    (f : Hom A B) (g1 : Hom B X) (g2 : Hom B Y),
        f .> fpair g1 g2 == fpair (f .> g1) (f .> g2).
Proof.
  destruct hp; simpl; intros. do 2 red in is_product0.
  destruct (is_product0 X Y A (f .> g1) (f .> g2)) as [_ H3].
  destruct (is_product0 X Y B g1 g2) as [[H1' H2'] _].
  rewrite <- H3.
    reflexivity.
    split.
      rewrite comp_assoc, <- H1'. reflexivity.
      rewrite comp_assoc, <- H2'. reflexivity.
Qed.

Theorem fpair_id : forall (C : Cat) (hp : has_products C) (X Y : Ob C),
    fpair proj1 proj2 == id (prodOb X Y).
Proof.
  destruct hp; simpl; intros. do 2 red in is_product0.
  destruct (is_product0 X Y (prodOb0 X Y) (proj3 X Y) (proj4 X Y))
    as [_ H3].
  rewrite H3.
    reflexivity.
    split; cat.
Qed.

Theorem fpair_comp :
  forall (C : Cat) (hp : has_products C) (A X Y X' Y' : Ob C)
    (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) ==
      fpair f g .> fpair (proj1 .> h1) (proj2 .> h2).
Proof.
  intros. rewrite fpair_pre. apply fpair_Proper.
    rewrite <- comp_assoc. rewrite fpair_proj1. reflexivity.
    rewrite <- comp_assoc. rewrite fpair_proj2. reflexivity.
Qed.

Ltac fpair_simpl :=
    repeat rewrite <- fpair_id;
    repeat rewrite fpair_pre;
    repeat rewrite <- comp_assoc;
    repeat (try rewrite fpair_proj1; try rewrite fpair_proj2).

Ltac fpair := let P := fresh "P" in pose (P := fpair_Proper); cat;
repeat match goal with
    | |- ?x == ?x => reflexivity
    | |- fpair _ _ == fpair _ _ => f_equiv
    | _ => fpair_simpl
end.

Theorem product_skolem_iso :
  forall (C : Cat) (X Y : Ob C)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P)
  (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y)
  (fpair' : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A Q),
    product_skolem C P p1 p2 fpair ->
    product_skolem C Q q1 q2 fpair' ->
    P ~ Q.
Proof.
  intros. red in H. red in H0.
  red. exists (fpair' _ p1 p2).
  red. exists (fpair0 _ q1 q2).
  destruct
    (H P p1 p2) as [[HP1 HP2] HP3],
    (H Q q1 q2) as [[HQ1 HQ2] HQ3],
    (H0 P p1 p2) as [[HP1' HP2'] HP3'],
    (H0 Q q1 q2) as [[HQ1' HQ2'] HQ3'].
  cat.
    rewrite <- (HP3 (fpair' P p1 p2 .> fpair0 Q q1 q2)).
      apply HP3. cat.
      cat.
        rewrite <- HQ1. assumption.
        rewrite <- HQ2. assumption.
    rewrite <- (HQ3' (fpair0 Q q1 q2 .> fpair' P p1 p2)).
      apply HQ3'. cat.
      cat.
        rewrite <- HP1'. assumption.
        rewrite <- HP2'. assumption.
Qed.

Theorem product_skolem_comm :
  forall (C : Cat) (X Y P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P),
      product_skolem C P p1 p2 fpair ->
      product_skolem C P p2 p1 (fun A f g => fpair A g f).
Proof.
  unfold product_skolem in *; intros.
  destruct (H X0 g f) as [[H1 H2] H3]. cat.
Qed.

Theorem prodOb_comm : forall (C : Cat) (hp : has_products C) (X Y : Ob C),
    prodOb X Y ~ prodOb Y X.
Proof.
  intros.
  red. exists (fpair proj2 proj1).
  red. exists (fpair proj2 proj1).
  split.
    rewrite <- fpair_id. rewrite fpair_pre. apply fpair_Proper.
      rewrite fpair_proj2. reflexivity.
      rewrite fpair_proj1. reflexivity.
    rewrite <- fpair_id. rewrite fpair_pre. apply fpair_Proper.
      rewrite fpair_proj2. reflexivity.
      rewrite fpair_proj1. reflexivity.
Restart.
  intros.
  red. exists (fpair proj2 proj1).
  red. exists (fpair proj2 proj1).
  fpair.
Qed.

(* TODO : dual *)
Theorem prodOb_assoc : forall (C : Cat) (hp : has_products C) (X Y Z : Ob C),
    prodOb X (prodOb Y Z) ~ prodOb (prodOb X Y) Z.
Proof.
  intros.
  red. exists (fpair (fpair proj1 (proj2 .> proj1)) (proj2 .> proj2)).
  red. exists (fpair (proj1 .> proj1) (fpair (proj1 .> proj2) proj2)).
  pose (P := fpair_Proper). split.
    fpair_simpl. f_equiv.
      destruct hp; simpl in *. edestruct is_product0; apply H0; cat.
    fpair_simpl. f_equiv.
      destruct hp; simpl in *. edestruct is_product0; apply H0; cat.
Restart.
  intros.
  red. exists (fpair (fpair proj1 (proj2 .> proj1)) (proj2 .> proj2)).
  red. exists (fpair (proj1 .> proj1) (fpair (proj1 .> proj2) proj2)).
  fpair; destruct hp; simpl in *; edestruct is_product0; apply H0; cat.
Defined.

Theorem copair_coproj1 :
  forall (C : Cat) (hp : has_coproducts C) (X Y A : Ob C)
    (f : Hom X A) (g : Hom Y A), coproj1 .> copair f g == f.
Proof.
  intros. destruct hp; simpl. do 2 red in is_coproduct0.
  destruct (is_coproduct0 X Y A f g) as [[H1 H2] H3].
  rewrite <- H1. reflexivity.
Qed.

Theorem copair_coproj2 :
  forall (C : Cat) (hp : has_coproducts C) (X Y A : Ob C)
    (f : Hom X A) (g : Hom Y A), coproj2 .> copair f g == g.
Proof.
  intros. destruct hp; simpl. do 2 red in is_coproduct0.
  destruct (is_coproduct0 X Y A f g) as [[H1 H2] H3].
  rewrite <- H2. reflexivity.
Qed.

Theorem copair_post :
  forall (C : Cat) (hp : has_coproducts C) (X Y A B : Ob C)
    (f1 : Hom X A) (f2 : Hom Y A) (g : Hom A B),
      copair f1 f2 .> g == copair (f1 .> g) (f2 .> g).
Proof.
  intros. destruct hp; simpl. do 2 red in is_coproduct0.
  destruct (is_coproduct0 X Y B (f1 .> g) (f2 .> g)) as [_ H3].
  destruct (is_coproduct0 X Y A f1 f2) as [[H1 H2] _].
  rewrite H3.
    reflexivity.
    split.
      rewrite <- comp_assoc, <- H1. reflexivity.
      rewrite <- comp_assoc, <- H2. reflexivity.
Qed.

Theorem copair_id :
  forall (C : Cat) (hp : has_coproducts C) (X Y : Ob C),
    copair coproj1 coproj2 == id (coprodOb X Y).
Proof.
  destruct hp; simpl; intros. do 2 red in is_coproduct0.
  destruct (is_coproduct0 X Y (coprodOb0 X Y) (coproj3 X Y) (coproj4 X Y))
    as [_ H3].
  apply H3. cat.
Qed.

Theorem copair_comp : 
  forall (C : Cat) (hp : has_coproducts C) (X Y X' Y' A : Ob C)
    (f : Hom X A) (g : Hom Y A) (h1 : Hom X' X) (h2 : Hom Y' Y),
      copair (h1 .> f) (h2 .> g) ==
      copair (h1 .> coproj1) (h2 .> coproj2) .> copair f g.
Proof.
  intros. rewrite copair_post. apply copair_Proper.
    rewrite comp_assoc. rewrite copair_coproj1. reflexivity.
    rewrite comp_assoc. rewrite copair_coproj2. reflexivity.
Qed.

Ltac copair_simpl :=
    repeat rewrite <- copair_id;
    repeat rewrite copair_post;
    repeat rewrite <- comp_assoc;
    repeat (try rewrite copair_coproj1; try rewrite copair_coproj2).

Ltac copair := let P := fresh "P" in pose (P := copair_Proper); cat;
repeat match goal with
    | |- ?x == ?x => reflexivity
    | |- copair _ _ == copair _ _ => f_equiv
    | _ => copair_simpl
end.

Theorem coproduct_skolem_comm :
  forall (C : Cat) (X Y P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      coproduct_skolem C P p1 p2 copair ->
      coproduct_skolem C P p2 p1 (fun A f g => copair A g f).
Proof.
  unfold coproduct_skolem in *; intros.
  destruct (H X0 g f) as [[H1 H2] H3]. cat.
Qed.

Theorem coprodOb_comm : forall (C : Cat) (hp : has_coproducts C) (X Y : Ob C),
    coprodOb X Y ~ coprodOb Y X.
Proof.
  intros.
  red. exists (copair coproj2 coproj1).
  red. exists (copair coproj2 coproj1).
  split.
    rewrite copair_post. rewrite <- copair_id. apply copair_Proper.
      apply copair_coproj2.
      apply copair_coproj1.
    rewrite copair_post. rewrite <- copair_id. apply copair_Proper.
      apply copair_coproj2.
      apply copair_coproj1.
Restart.
  intros.
  red. exists (copair coproj2 coproj1).
  red. exists (copair coproj2 coproj1).
  copair.
Qed.

(* TODO *) Theorem coprodOb_assoc :
  forall (C : Cat) (hp : has_coproducts C) (X Y Z : Ob C),
    coprodOb X (coprodOb Y Z) ~ coprodOb (coprodOb X Y) Z.
Proof.
  intros.
  red. pose (wut := @copair C hp X (coprodOb Y Z)
    (coprodOb (coprodOb X Y) Z) (coproj1 .> coproj1)).
Abort.

Definition ProdCatHom {C D : Cat} (X Y : Ob C * Ob D) :=
    prod (Hom (fst X) (fst Y)) (Hom (snd X) (snd Y)).

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

Instance CAT_prod (C : Cat) (D : Cat) : Cat :=
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
      (fpair (proj1 .> f) (proj2 .> g)).

Theorem ProductFunctor_fmap_Proper : forall (C : Cat)
    (hp : has_products C) (X X' Y Y' : Ob C),
    Proper ((@equiv _ (HomSetoid X Y))  ==>
      (@equiv _ (HomSetoid X' Y'))  ==>
      (@equiv _ (HomSetoid (prodOb X X') (prodOb Y Y'))))
      (@ProductFunctor_fmap C hp X X' Y Y').
Proof.
  unfold Proper, respectful, ProductFunctor_fmap. intros.
  apply fpair_Proper.
    rewrite H. reflexivity.
    rewrite H0. reflexivity.
Qed.

Theorem ProductFunctor_fmap_pres_id : forall (C : Cat)
    (hp : has_products C) (X Y : Ob C),
    ProductFunctor_fmap (id X) (id Y) == id (prodOb X Y).
Proof.
  intros; unfold ProductFunctor_fmap.
  rewrite <- fpair_id. apply fpair_Proper; cat.
Defined.

Theorem ProductFunctor_fmap_pres_comp : forall (C : Cat)
    (hp : has_products C) (A1 A2 B1 B2 C1 C2 : Ob C)
    (f1 : Hom A1 B1) (g1 : Hom B1 C1) (f2 : Hom A2 B2) (g2 : Hom B2 C2),
    ProductFunctor_fmap (f1 .> g1) (f2 .> g2) ==
    ProductFunctor_fmap f1 f2 .> ProductFunctor_fmap g1 g2.
Proof.
  unfold ProductFunctor_fmap; intros.
  rewrite fpair_pre. apply fpair_Proper.
    cat. rewrite fpair_proj1. cat.
    cat. rewrite fpair_proj2. cat.
Defined.

Theorem ProductFunctor_fmap_pres_comp_l :
    forall {C : Cat} {hp : has_products C} {X Y : Ob C}
    (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
    ProductFunctor_fmap (f .> g) (id Z) == 
    ProductFunctor_fmap f (id Z) .> ProductFunctor_fmap g (id Z).
Proof.
  intros. rewrite <- ProductFunctor_fmap_pres_comp.
  apply (ProductFunctor_fmap_Proper); cat.
Defined.

Theorem ProductFunctor_fmap_pres_comp_r :
    forall {C : Cat} {hp : has_products C} {X Y : Ob C}
    (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
    ProductFunctor_fmap (id Z) (f .> g) ==
    ProductFunctor_fmap (id Z) f .> ProductFunctor_fmap (id Z) g.
Proof.
  intros. rewrite <- ProductFunctor_fmap_pres_comp.
  apply (ProductFunctor_fmap_Proper); cat.
Defined.

Instance ProductFunctor {C : Cat} {hp : has_products C} :
    Functor (CAT_prod C C) C :=
{
    fob := fun P : Ob (CAT_prod C C) => prodOb (fst P) (snd P);
    fmap := fun (X Y : Ob (CAT_prod C C)) (f : Hom X Y) =>
      ProductFunctor_fmap (fst f) (snd f)
}.
Proof.
  do 2 red; simpl; intros. destruct H, hp; simpl.
    rewrite H, H0. reflexivity.
  intros. apply ProductFunctor_fmap_pres_comp.
  intros. apply ProductFunctor_fmap_pres_id.
Defined.

Definition CoproductFunctor_fmap {C : Cat} {hp : has_coproducts C}
    {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
      : Hom (coprodOb X X') (coprodOb Y Y') :=
      (copair (f .> coproj1) (g .> coproj2)).

Instance CoproductFunctor {C : Cat} (hp : has_coproducts C) :
    Functor (CAT_prod C C) C :=
{
    fob := fun P : Ob (CAT_prod C C) => coprodOb (fst P) (snd P);
    fmap := fun (X Y : Ob (CAT_prod C C)) (f : Hom X Y) =>
      CoproductFunctor_fmap (fst f) (snd f)
}.
Proof.
  all: unfold CoproductFunctor_fmap.
  proper. destruct H. apply copair_Proper.
    rewrite H. reflexivity.
    rewrite H0. reflexivity.
  intros. rewrite copair_post. apply copair_Proper.
    cat. rewrite copair_coproj1. reflexivity.
    cat. rewrite copair_coproj2. reflexivity.
  intros. rewrite <- copair_id. apply copair_Proper; cat.
Defined.

(* TODO *)
Notation "A × B" := (fob ProductFunctor (A, B)) (at level 40).
Notation "f ×' g" := (fmap ProductFunctor f g) (at level 40).

Instance Dual_has_coproducts (C : Cat) (hp : has_products C)
    : has_coproducts (Dual C) :=
{
    coprodOb := @prodOb C hp;
    coproj1 := @proj1 C hp;
    coproj2 := @proj2 C hp;
    copair := @fpair C hp
}.
Proof.
  (* Proper *) simpl. apply fpair_Proper.
  (* Coproduct laws *) apply (@is_product C hp).
Defined.

Instance Dual_has_products (C : Cat) (hp : has_coproducts C)
    : has_products (Dual C) :=
{
    prodOb := @coprodOb C hp;
    proj1 := @coproj1 C hp;
    proj2 := @coproj2 C hp;
    fpair := @copair C hp;
}.
Proof.
  (* Proper *) simpl. apply copair_Proper.
  (* Products laws *) apply (@is_coproduct C hp).
Defined.

Instance Dual_has_biproducts (C : Cat) (hp : has_biproducts C)
    : has_biproducts (Dual C) :=
{
    products := Dual_has_products C hp;
    coproducts := Dual_has_coproducts C hp;
}.
Proof. simpl. intros. rewrite product_is_coproduct. auto. Defined.