From Cat Require Export Cat.
From Cat Require Export Tactics.FunctorTactic.

Set Implicit Arguments.

Definition product
  (C : Cat) {A B : Ob C}
  (P : Ob C) (p1 : Hom P A) (p2 : Hom P B)
  (fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P)
  : Prop :=
    forall (X : Ob C) (f : Hom X A) (g : Hom X B),
      setoid_unique (fun u : Hom X P => f == u .> p1 /\ g == u .> p2) (fpair f g).

Definition coproduct
  (C : Cat) {A B : Ob C}
  (P : Ob C) (p1 : Hom A P) (p2 : Hom B P)
  (copair : forall {X : Ob C} (f : Hom A X) (g : Hom B X), Hom P X)
  : Prop :=
    forall (X : Ob C) (f : Hom A X) (g : Hom B X),
      setoid_unique (fun d : Hom P X => f == p1 .> d /\ g == p2 .> d) (copair f g).

Definition biproduct
  (C : Cat) {A B : Ob C} (P : Ob C)
  (pA : Hom P A) (pB : Hom P B) (iA : Hom A P) (iB : Hom B P)
  (fpair : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P)
  (copair : forall {X : Ob C} (f : Hom A X) (g : Hom B X), Hom P X)
  : Prop := product C P pA pB (@fpair) /\ coproduct C P iA iB (@copair).

Class HasProducts (C : Cat) : Type :=
{
  prodOb : Ob C -> Ob C -> Ob C;
  proj1 : forall A B : Ob C, Hom (prodOb A B) A;
  proj2 : forall A B : Ob C, Hom (prodOb A B) B;
  fpair : forall {A B X : Ob C} (f : Hom X A) (g : Hom X B), Hom X (prodOb A B);
  Proper_fpair :> forall (A B X : Ob C), Proper (equiv ==> equiv ==> equiv) (@fpair A B X);
  is_product :
    forall (A B : Ob C), product C (prodOb A B) (proj1 A B) (proj2 A B) (@fpair A B)
}.

Arguments prodOb {C HasProducts} _ _.
Arguments proj1  {C HasProducts A B}.
Arguments proj2  {C HasProducts A B}.
Arguments fpair  {C HasProducts A B X} _ _.

Class HasCoproducts (C : Cat) : Type :=
{
  coprodOb : Ob C -> Ob C -> Ob C;
  coproj1 : forall A B : Ob C, Hom A (coprodOb A B);
  coproj2 : forall A B : Ob C, Hom B (coprodOb A B);
  copair : forall {A B X : Ob C} (f : Hom A X) (g : Hom B X), Hom (coprodOb A B) X;
  Proper_copair :> forall (A B X : Ob C), Proper (equiv ==> equiv ==> equiv) (@copair A B X);
  is_coproduct :
    forall A B : Ob C, coproduct C (coprodOb A B) (coproj1 A B) (coproj2 A B) (@copair A B)
}.

Arguments coprodOb {C HasCoproducts} _ _.
Arguments coproj1  {C HasCoproducts A B}.
Arguments coproj2  {C HasCoproducts A B}.
Arguments copair   {C HasCoproducts A B X} _ _.

Class HasBiproducts (C : Cat) : Type :=
{
  products :> HasProducts C;
  coproducts :> HasCoproducts C;
  product_is_coproduct : forall X Y : Ob C, prodOb X Y = coprodOb X Y
}.

Coercion products : HasBiproducts >-> HasProducts.
Coercion coproducts : HasBiproducts >-> HasCoproducts.

#[export]
Instance HasCoproducts_Dual (C : Cat) (hp : HasProducts C) : HasCoproducts (Dual C) :=
{
  coprodOb := @prodOb C hp;
  coproj1 := @proj1 C hp;
  coproj2 := @proj2 C hp;
  copair := @fpair C hp;
  Proper_copair := @Proper_fpair C hp;
  is_coproduct := @is_product C hp
}.

#[export]
Instance HasProducts_Dual (C : Cat) (hp : HasCoproducts C) : HasProducts (Dual C) :=
{
  prodOb := @coprodOb C hp;
  proj1 := @coproj1 C hp;
  proj2 := @coproj2 C hp;
  fpair := @copair C hp;
  Proper_fpair := @Proper_copair C hp;
  is_product := @is_coproduct C hp
}.

#[refine]
#[export]
Instance HasBiproducts_Dual (C : Cat) (hp : HasBiproducts C) : HasBiproducts (Dual C) :=
{
  products := HasProducts_Dual hp;
  coproducts := HasCoproducts_Dual hp;
}.
Proof.
  simpl. intros. rewrite product_is_coproduct. trivial.
Defined.

Lemma dual_product_coproduct :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (fpair : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P),
      product C P p1 p2 fpair
        <->
      coproduct (Dual C) P p1 p2 fpair.
Proof. cat. Defined.

Lemma dual_biproduct_self :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y) (q1 : Hom X P) (q2 : Hom Y P)
    (fpair : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P)
    (copair : forall (P' : Ob C) (q1' : Hom X P') (q2' : Hom Y P'), Hom P P'),
      biproduct C P p1 p2 q1 q2 fpair copair
        <->
      biproduct (Dual C) P q1 q2 p1 p2 copair fpair.
Proof.
  unfold biproduct. cat.
Qed.

Lemma fpair_proj1 :
  forall (C : Cat) (hp : HasProducts C) (X Y A : Ob C) (f : Hom A X) (g : Hom A Y),
    fpair f g .> proj1 == f.
Proof.
  destruct hp; cbn; intros. do 2 red in is_product0.
  destruct (is_product0 X Y A f g) as [[H1 H2] H3].
  rewrite <- H1. reflexivity.
Qed.

Lemma fpair_proj2 :
  forall (C : Cat) (hp : HasProducts C) (X Y A : Ob C) (f : Hom A X) (g : Hom A Y),
    fpair f g .> proj2 == g.
Proof.
  destruct hp; cbn; intros. do 2 red in is_product0.
  destruct (is_product0 X Y A f g) as [[H1 H2] H3].
  rewrite <- H2. reflexivity.
Qed.

Lemma fpair_pre :
  forall
    (C : Cat) (hp : HasProducts C)
    (A B X Y : Ob C) (f : Hom A B) (g1 : Hom B X) (g2 : Hom B Y),
      f .> fpair g1 g2 == fpair (f .> g1) (f .> g2).
Proof.
  destruct hp; cbn; intros. do 2 red in is_product0.
  destruct (is_product0 X Y A (f .> g1) (f .> g2)) as [_ H3].
  destruct (is_product0 X Y B g1 g2) as [[H1' H2'] _].
  rewrite <- H3.
    reflexivity.
    split.
      rewrite comp_assoc, <- H1'. reflexivity.
      rewrite comp_assoc, <- H2'. reflexivity.
Qed.

Lemma fpair_id :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C),
    fpair proj1 proj2 == id (prodOb X Y).
Proof.
  destruct hp; cbn; intros. do 2 red in is_product0.
  destruct (is_product0 X Y (prodOb0 X Y) (proj3 X Y) (proj4 X Y))
    as [_ H3].
  rewrite H3.
    reflexivity.
    split; cat.
Qed.

Lemma fpair_comp :
  forall
    (C : Cat) (hp : HasProducts C) (A X Y X' Y' : Ob C)
    (f : Hom A X) (g : Hom A Y) (h1 : Hom X X') (h2 : Hom Y Y'),
      fpair (f .> h1) (g .> h2) == fpair f g .> fpair (proj1 .> h1) (proj2 .> h2).
Proof.
  intros. rewrite fpair_pre, <- ?comp_assoc, ?fpair_proj1, ?fpair_proj2. reflexivity.
Qed.

Lemma fpair_pre_id :
  forall (C : Cat) (hp : HasProducts C) (A X Y : Ob C) (f : Hom A (prodOb X Y)),
    fpair (f .> proj1) (f .> proj2) == f.
Proof.
  intros. rewrite <- fpair_pre, fpair_id, comp_id_r. reflexivity.
Qed.

Ltac fpair := intros; try split;
repeat match goal with
| |- context [fpair (_ .> proj1) (_ .> proj2)] => rewrite <- fpair_pre, fpair_id
| |- context [_ .> fpair _ _] => rewrite fpair_pre
| |- context [fpair _ _ .> proj1] => rewrite fpair_proj1
| |- context [fpair _ _ .> proj2] => rewrite fpair_proj2
| |- context [fpair proj1 proj2] => rewrite fpair_id
| |- ?x == ?x => reflexivity
| |- fpair _ _ == fpair _ _ => apply Proper_fpair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- fpair _ _ == id (prodOb _ _) => rewrite <- fpair_id; apply Proper_fpair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite <- ?comp_assoc; auto
end.

#[global] Hint Rewrite fpair_pre_id fpair_pre fpair_proj1 fpair_proj2 fpair_id : fpair'_base.

Ltac fpair' := autorewrite with fpair'_base.

Module Wut.

#[refine]
#[export]
Instance Simplify_fpair_proj1
  (C : Cat) (hp : HasProducts C) (X Y Z : Ob C) (f : Hom X Y) (g : Hom X Z)
  : Simplify (Comp (Var (fpair f g)) (Var proj1)) | 1 :=
{
  simplify := Var f
}.
Proof.
  cbn. rewrite fpair_proj1. reflexivity.
Defined.

#[refine]
#[export]
Instance Simplify_fpair_proj2
  (C : Cat) (hp : HasProducts C) (X Y Z : Ob C) (f : Hom X Y) (g : Hom X Z)
  : Simplify (Comp (Var (fpair f g)) (Var proj2)) | 1 :=
{
  simplify := Var g
}.
Proof.
  cbn. rewrite fpair_proj2. reflexivity.
Defined.

#[refine]
#[export]
Instance Simplify_fpair_id
  (C : Cat) (hp : HasProducts C) (X Y Z : Ob C) (f : Hom X Y) (g : Hom X Z)
  : Simplify (Var (fpair proj1 proj2)) | 1 :=
{
  simplify := Id (prodOb X Y)
}.
Proof.
  cbn. rewrite fpair_id. reflexivity.
Defined.

Goal
  forall (C : Cat) (hp : HasProducts C) (X Y Z : Ob C),
    fpair (@proj1 _ _ X Y) proj2 .> proj1 == proj1.
Proof.
  intros. reflect_cat. reflexivity.
Qed.

End Wut.

Module Tactic.

Inductive exp {C : Cat} {hp : HasProducts C} : Ob C -> Ob C -> Type :=
| Id    : forall X : Ob C, exp X X
| Var   : forall X Y : Ob C, Hom X Y -> exp X Y
| Comp  : forall X Y Z : Ob C, exp X Y -> exp Y Z -> exp X Z
| Proj1 : forall X Y : Ob C, exp (prodOb X Y) X
| Proj2 : forall X Y : Ob C, exp (prodOb X Y) Y
| Fpair : forall A B X : Ob C, exp X A -> exp X B -> exp X (prodOb A B).

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
| Proj1       => proj1
| Proj2       => proj2
| Fpair e1 e2 => fpair (expDenote e1) (expDenote e2)
end.

(* TODO: class-based simplification *)

End Tactic.

Lemma product_uiso :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P)
    (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y)
    (fpair' : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A Q),
      product C P p1 p2 fpair -> product C Q q1 q2 fpair' ->
        exists!! f : Hom P Q, isIso f /\ p1 == f .> q1 /\ p2 == f .> q2.
Proof.
  intros. do 2 red in H. do 2 red in H0.
  exists (fpair' _ p1 p2).
  red. repeat split.
    exists (fpair0 _ q1 q2).
      destruct
        (H P p1 p2) as [[HP1 HP2] HP3],
        (H Q q1 q2) as [[HQ1 HQ2] HQ3],
        (H0 P p1 p2) as [[HP1' HP2'] HP3'],
        (H0 Q q1 q2) as [[HQ1' HQ2'] HQ3'].
      split.
        rewrite <- (HP3 (fpair' P p1 p2 .> fpair0 Q q1 q2)).
          apply HP3. cat.
          split; assocr.
            rewrite <- HQ1. assumption.
            rewrite <- HQ2. assumption.
        rewrite <- (HQ3' (fpair0 Q q1 q2 .> fpair' P p1 p2)).
          apply HQ3'. cat.
          split; assocr.
            rewrite <- HP1'. assumption.
            rewrite <- HP2'. assumption.
    edestruct H0 as [[H1 H2] _]. eauto.
    edestruct H0 as [[H1 H2] _]. eauto.
    intros. destruct H1 as [[y_inv [iso1 iso2]] [eq1 eq2]].
      edestruct H0. apply H2. cat.
Qed.

Lemma product_iso :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P)
    (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y)
    (fpair' : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A Q),
      product C P p1 p2 fpair -> product C Q q1 q2 fpair' -> P ~ Q.
Proof.
  intros. destruct (product_uiso H H0). cat.
Qed.

Lemma product_fpair_equiv :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P)
    (fpair' : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P),
      product C P p1 p2 fpair -> product C P p1 p2 fpair' ->
        forall (A : Ob C) (f : Hom A X) (g : Hom A Y),
          fpair A f g == fpair' A f g.
Proof.
  intros. edestruct H, H0. cat.
Qed.

Lemma product_p1_equiv
  (C : Cat) (X Y : Ob C)
  (P : Ob C) (p1 : Hom P X) (p1' : Hom P X) (p2 : Hom P Y)
  (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P) :
    product C P p1 p2 fpair -> product C P p1' p2 fpair -> p1 == p1'.
Proof.
  intros. do 2 red in H.
  destruct (H P p1 p2) as [[H1 H2] H3].
  destruct (H0 P p1 p2) as [[H1' H2'] H3'].
  rewrite (H3 (id P)) in H1'. cat. cat.
Qed.

Lemma product_p2_equiv :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y) (p2' : Hom P Y)
    (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P),
    product C P p1 p2 fpair -> product C P p1 p2' fpair -> p2 == p2'.
Proof.
  intros. do 2 red in H.
  destruct (H P p1 p2) as [[H1 H2] H3].
  destruct (H0 P p1 p2) as [[H1' H2'] H3'].
  rewrite (H3 (id P)) in H2'. cat. cat.
Qed.

(* TODO : Dual *) Lemma iso_to_prod :
  forall
    (C : Cat) (X Y : Ob C)
    (P Q : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (fpair : forall Q : Ob C, Hom Q X -> Hom Q Y -> Hom Q P),
      product C P p1 p2 fpair ->
      forall (f : Hom Q P) (H : isIso f),
      product C Q (f .> p1) (f .> p2)
        (fun (A : Ob C) (p1' : Hom A X) (p2' : Hom A Y) =>
          match constructive_indefinite_description _ H with
          | exist _ g _ => fpair A p1' p2' .> g
          end).
Proof.
  unfold product in *. intros.
  destruct (constructive_indefinite_description _ _) as (f_inv & eq1 & eq2).
  edestruct H as [[H1 H2] H3]. repeat split.
    rewrite comp_assoc, <- (comp_assoc f_inv f).
      rewrite eq2. cat.
    rewrite comp_assoc, <- (comp_assoc f_inv f).
      rewrite eq2. cat.
    intros. red in H. destruct (H _ f0 g) as [[H1' H2'] H3'].
      specialize (H3' (y .> f)). rewrite H3'; cat.
        rewrite eq1. cat.
Qed.

Lemma product_comm :
  forall
    (C : Cat) (X Y P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
    (fpair : forall (A : Ob C) (f : Hom A X) (g : Hom A Y), Hom A P),
      product C P p1 p2 fpair -> product C P p2 p1 (fun A f g => fpair A g f).
Proof.
  unfold product in *; intros.
  destruct (H X0 g f) as [[H1 H2] H3]. cat.
Qed.

(* TODO: TESTS *)

Lemma prodOb_comm :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C),
    prodOb X Y ~ prodOb Y X.
Proof.
  intros.
  red. exists (fpair proj2 proj1).
  red. exists (fpair proj2 proj1).
  fpair.
Qed.

Lemma prodOb_assoc :
  forall (C : Cat) (hp : HasProducts C) (X Y Z : Ob C),
    prodOb X (prodOb Y Z) ~ prodOb (prodOb X Y) Z.
Proof.
  intros.
  red. exists (fpair (fpair proj1 (proj2 .> proj1)) (proj2 .> proj2)).
  red. exists (fpair (proj1 .> proj1) (fpair (proj1 .> proj2) proj2)).
  fpair.
Defined.

Lemma prodOb_assoc' :
  forall (C : Cat) (hp : HasProducts C) (X Y Z : Ob C),
    {f : Hom (prodOb (prodOb X Y) Z) (prodOb X (prodOb Y Z)) | isIso f}.
Proof.
  intros.
  exists (fpair (proj1 .> proj1) (fpair (proj1 .> proj2) proj2)).
  red. exists (fpair (fpair proj1 (proj2 .> proj1)) (proj2 .> proj2)).
  fpair.
Defined.

Lemma copair_coproj1 :
  forall (C : Cat) (hp : HasCoproducts C) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
    coproj1 .> copair f g == f.
Proof.
  intros. destruct hp; cbn. do 2 red in is_coproduct0.
  destruct (is_coproduct0 X Y A f g) as [[H1 H2] H3].
  rewrite <- H1. reflexivity.
Qed.

Lemma copair_coproj2 :
  forall (C : Cat) (hp : HasCoproducts C) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A),
    coproj2 .> copair f g == g.
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
    copair coproj1 coproj2 == id (coprodOb X Y).
Proof.
  destruct hp; cbn; intros. do 2 red in is_coproduct0.
  destruct (is_coproduct0 X Y (coprodOb0 X Y) (coproj3 X Y) (coproj4 X Y))
    as [_ H3].
  apply H3. cat.
Qed.

Lemma copair_comp : 
  forall
    (C : Cat) (hp : HasCoproducts C)
    (X Y X' Y' A : Ob C) (f : Hom X A) (g : Hom Y A) (h1 : Hom X' X) (h2 : Hom Y' Y),
      copair (h1 .> f) (h2 .> g) == copair (h1 .> coproj1) (h2 .> coproj2) .> copair f g.
Proof.
  intros. rewrite copair_post, !comp_assoc, copair_coproj1, copair_coproj2. reflexivity.
Qed.

Ltac copair := intros; try split;
repeat match goal with
| |- context [copair (coproj1 .> ?x) (coproj2 .> ?x)] => rewrite <- copair_post, copair_id
| |- context [copair _ _ .> _] => rewrite copair_post
| |- context [coproj1 .> copair _ _] => rewrite copair_coproj1
| |- context [coproj2 .> copair _ _] => rewrite copair_coproj2
| |- context [copair coproj1 coproj2] => rewrite copair_id
| |- ?x == ?x => reflexivity
| |- copair _ _ == copair _ _ => apply Proper_copair
| |- context [id _ .> _] => rewrite comp_id_l
| |- context [_ .> id _] => rewrite comp_id_r
| |- copair _ _ == id (coprodOb _ _) => rewrite <- copair_id; apply Proper_copair
| |- ?f .> ?g == ?f .> ?g' => f_equiv
| |- ?f .> ?g == ?f' .> ?g => f_equiv
| _ => rewrite ?comp_assoc; auto
end.

Lemma coproduct_uiso :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A)
    (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q)
    (copair' : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom Q A),
      coproduct C P p1 p2 copair -> coproduct C Q q1 q2 copair' ->
        exists!! f : Hom P Q, isIso f /\ p1 .> f == q1 /\ p2 .> f == q2.
Proof.
  intros. do 2 red in H. do 2 red in H0.
  exists (copair0 _ q1 q2).
  red. repeat split.
    exists (copair' _ p1 p2).
      destruct
        (H P p1 p2) as [[HP1 HP2] HP3],
        (H Q q1 q2) as [[HQ1 HQ2] HQ3],
        (H0 P p1 p2) as [[HP1' HP2'] HP3'],
        (H0 Q q1 q2) as [[HQ1' HQ2'] HQ3'].
      cat.
        rewrite <- (HP3 (copair0 Q q1 q2 .> copair' P p1 p2)).
          apply HP3. cat.
          cat; rewrite <- comp_assoc.
            rewrite <- HQ1. assumption.
            rewrite <- HQ2. assumption.
        rewrite <- (HQ3' (copair' P p1 p2 .> copair0 Q q1 q2)).
          apply HQ3'. cat.
          cat; rewrite <- comp_assoc.
            rewrite <- HP1'. assumption.
            rewrite <- HP2'. assumption.
    edestruct H as [[H1 H2] _]. rewrite <- H1. reflexivity.
    edestruct H as [[H1 H2] _]. rewrite <- H2. reflexivity.
    intros. destruct H1 as [[y_inv [iso1 iso2]] [eq1 eq2]].
      edestruct H. apply H2. split; [rewrite eq1 | rewrite eq2]; cat.
Qed.

Lemma coproduct_iso :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A)
    (Q : Ob C) (q1 : Hom X Q) (q2 : Hom Y Q)
    (copair' : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom Q A),
      coproduct C P p1 p2 copair -> coproduct C Q q1 q2 copair' -> P ~ Q.
Proof.
  intros. destruct (coproduct_uiso H H0). cat.
Qed.

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

Lemma coproduct_p1_equiv :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom X P) (p1' : Hom X P) (p2 : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      coproduct C P p1 p2 copair -> coproduct C P p1' p2 copair -> p1 == p1'.
Proof.
  intros. do 2 red in H.
  destruct (H P p1 p2) as [[H1 H2] H3].
  destruct (H0 P p1 p2) as [[H1' H2'] H3'].
  rewrite (H3 (id P)) in H1'. cat. cat.
Qed.

Lemma coproduct_p2_equiv :
  forall
    (C : Cat) (X Y : Ob C)
    (P : Ob C) (p1 : Hom X P) (p2 : Hom Y P) (p2' : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      coproduct C P p1 p2 copair -> coproduct C P p1 p2' copair -> p2 == p2'.
Proof.
  intros. do 2 red in H.
  destruct (H P p1 p2) as [[H1 H2] H3].
  destruct (H0 P p1 p2) as [[H1' H2'] H3'].
  rewrite (H3 (id P)) in H2'. cat. cat.
Qed.

Lemma coproduct_comm :
  forall
    (C : Cat) (X Y P : Ob C) (p1 : Hom X P) (p2 : Hom Y P)
    (copair : forall (A : Ob C) (f : Hom X A) (g : Hom Y A), Hom P A),
      coproduct C P p1 p2 copair -> coproduct C P p2 p1 (fun A f g => copair A g f).
Proof.
  unfold coproduct in *; intros.
  destruct (H X0 g f) as [[H1 H2] H3]. cat.
Qed.

Lemma coprodOb_comm :
  forall (C : Cat) (hp : HasCoproducts C) (X Y : Ob C),
    coprodOb X Y ~ coprodOb Y X.
Proof.
  intros.
  red. exists (copair coproj2 coproj1).
  red. exists (copair coproj2 coproj1).
  copair.
Qed.

Lemma coprodOb_assoc :
  forall (C : Cat) (hp : HasCoproducts C) (X Y Z : Ob C),
    coprodOb X (coprodOb Y Z) ~ coprodOb (coprodOb X Y) Z.
Proof.
  intros.
  red. exists (copair (coproj1 .> coproj1) (copair (coproj2 .> coproj1) coproj2)).
  red. exists (copair (copair coproj1 (coproj1 .> coproj2)) (coproj2 .> coproj2)).
  copair.
Qed.

Lemma coprodOb_assoc' :
  forall (C : Cat) (hp : HasCoproducts C) (X Y Z : Ob C),
    {f : Hom (coprodOb (coprodOb X Y) Z) (coprodOb X (coprodOb Y Z)) | isIso f}.
Proof.
  intros.
  exists (copair (copair coproj1 (coproj1 .> coproj2)) (coproj2 .> coproj2)).
  red. exists (copair (coproj1 .> coproj1) (copair (coproj2 .> coproj1) coproj2)).
  copair.
Defined.

Definition ProductFunctor_fmap
  {C : Cat} {hp : HasProducts C}
  {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
  : Hom (prodOb X X') (prodOb Y Y') :=
    fpair (proj1 .> f) (proj2 .> g).

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

Lemma ProductFunctor_fmap_id :
  forall (C : Cat) (hp : HasProducts C) (X Y : Ob C),
    ProductFunctor_fmap (id X) (id Y) == id (prodOb X Y).
Proof.
  intros; unfold ProductFunctor_fmap. fpair.
Defined.

Lemma ProductFunctor_fmap_comp :
  forall
    (C : Cat) (hp : HasProducts C)
    (A1 A2 B1 B2 C1 C2 : Ob C) (f1 : Hom A1 B1) (g1 : Hom B1 C1) (f2 : Hom A2 B2) (g2 : Hom B2 C2),
      ProductFunctor_fmap (f1 .> g1) (f2 .> g2)
        ==
      ProductFunctor_fmap f1 f2 .> ProductFunctor_fmap g1 g2.
Proof.
  unfold ProductFunctor_fmap. fpair.
Defined.

Lemma ProductFunctor_fmap_comp_l :
  forall
    {C : Cat} {hp : HasProducts C}
    {X Y : Ob C} (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
      ProductFunctor_fmap (f .> g) (id Z)
        == 
      ProductFunctor_fmap f (id Z) .> ProductFunctor_fmap g (id Z).
Proof.
  intros. rewrite <- ProductFunctor_fmap_comp. cat.
Defined.

Lemma ProductFunctor_fmap_comp_r :
  forall
    {C : Cat} {hp : HasProducts C}
    {X Y : Ob C} (Z : Ob C) (f : Hom X Y) (g : Hom Y X),
      ProductFunctor_fmap (id Z) (f .> g)
        ==
      ProductFunctor_fmap (id Z) f .> ProductFunctor_fmap (id Z) g.
Proof.
  intros. rewrite <- ProductFunctor_fmap_comp. cat.
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

Definition CoproductFunctor_fmap
  {C : Cat} {hp : HasCoproducts C}
  {X X' Y Y' : Ob C} (f : Hom X Y) (g : Hom X' Y')
  : Hom (coprodOb X X') (coprodOb Y Y')
  := (copair (f .> coproj1) (g .> coproj2)).

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

Notation "A × B" := (fob ProductFunctor (A, B)) (at level 40).
Notation "f ×' g" := (ProductFunctor_fmap f g) (at level 40).
Notation "A + B" := (fob CoproductFunctor (A, B)).
Notation "f +' g" := (CoproductFunctor_fmap f g) (at level 40).

#[refine]
#[export]
Instance ProductBifunctor {C : Cat} {hp : HasProducts C} : Bifunctor C C C :=
{
  biob := fun X Y : Ob C => prodOb X Y;
  bimap :=
    fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') => fpair (proj1 .> f) (proj2 .> g);
}.
Proof.
  unfold Proper, respectful. all: fpair.
Defined.

#[refine]
#[export]
Instance CoproductBifunctor {C : Cat} {hp : HasCoproducts C} : Bifunctor C C C :=
{
  biob := @coprodOb C hp;
  bimap :=
    fun (X Y X' Y' : Ob C) (f : Hom X Y) (g : Hom X' Y') => copair (f .> coproj1) (g .> coproj2)
}.
Proof.
  unfold Proper, respectful. all: copair.
Defined.