Require Export Cat.
Require Export Functor.

Open Scope type_scope.

Set Universe Polymorphism.

Definition product (C : Cat) {A B : Ob C} (P : Ob C) (p1 : Hom P A)
    (p2 : Hom P B) := forall (X : Ob C) (f : Hom X A) (g : Hom X B),
    exists!! u : Hom X P, f == u .> p1 /\ g == u .> p2.

Definition coproduct (C : Cat) {A B : Ob C} (P : Ob C) (iA : Hom A P)
    (iB : Hom B P) := forall (X : Ob C) (f : Hom A X) (g : Hom B X),
    exists!! u : Hom P X, f == iA .> u /\ g == iB .> u.

Definition has_binary_products (C : Cat) : Prop := forall (A B : Ob C),
    exists (P : Ob C) (pA : Hom P A) (pB : Hom P B), product C P pA pB.

Definition has_binary_coproducts (C : Cat) : Prop := forall (A B : Ob C),
    exists (P : Ob C) (iA : Hom A P) (iB : Hom B P), coproduct C P iA iB.

Class has_products (C : Cat) : Type :=
{
    prod' : Ob C -> Ob C -> Ob C;
    proj1' : forall A B : Ob C, Hom (prod' A B) A;
    proj2' : forall A B : Ob C, Hom (prod' A B) B;
    is_prod : forall A B : Ob C, product C (prod' A B) (proj1' A B) (proj2' A B)
}.

Definition ProdCatHom {C : Cat} (A B : Ob C * Ob C) :=
    prod (Hom (fst A) (fst B)) (Hom (snd A) (snd B)).
Print equiv.
Definition ProdCatSetoid {C : Cat} (A B : Ob C * Ob C)
    : Setoid (ProdCatHom A B).
refine
{|
    equiv := fun f g : ProdCatHom A B =>
        @equiv (@Hom C (fst A) (fst B)) (@HomSetoid C (fst A) (fst B))
        (fst f) (fst g) /\
        @equiv (@Hom C (snd A) (snd B)) (@HomSetoid C (snd A) (snd B))
        (snd f) (snd g)
|}.
Proof.
  split; red; intros; split; try destruct H; try destruct H0;
  try rewrite H; try rewrite H1; try rewrite H0; auto; reflexivity. 
Defined.

Instance CAT_prod (C : Cat) : Cat.
refine
{|
    Ob := Ob C * Ob C;
    Hom := ProdCatHom;
    HomSetoid := ProdCatSetoid;
    comp := fun (A B C : Ob C * Ob C)
        (f : Hom (fst A) (fst B) * Hom (snd A) (snd B))
        (g : Hom (fst B) (fst C) * Hom (snd B) (snd C)) =>
        (fst f .> fst g, snd f .> snd g);
    id := fun A : Ob C * Ob C => (id (fst A), id (snd A))
|}.
Proof.
(* Composition respects equivalence *)
  do 3 red; unfold equiv, ProdCatSetoid; intros.
    destruct x, x0, y, y0; split; simpl in *; destruct H, H0;
      try rewrite H; try rewrite H0; try rewrite H1; try rewrite H2;
        reflexivity.
(* Category axioms *)
  all: cat.
Defined.

(*Instance CAT_prod : has_products CAT :=
{
  prod' := 
}.*)

Class has_prod_functor (C : Cat) : Type :=
{
  prod_functor : Functor (CAT_prod C) C;
  proj1'' : forall A B : Ob C, Hom (prod_functor (A, B)) A;
  proj2'' : forall A B : Ob C, Hom (prod_functor (A, B)) B;
  is_prod' : forall A B : @Ob C,
    product C (@fob (CAT_prod C) C prod_functor (A, B))
    (proj1'' A B) (proj2'' A B)
}.
Print fmap.
Arguments fmap [C] [D] _ [A] [B] _.
Print fmap.
Notation "A × B" := (prod_functor (A, B)) (at level 40).
Notation "f ×' g" := (fmap prod_functor f g) (at level 40). (* (fmap (f, g)) (at level 40).*)

Class has_coproducts (C : Cat) : Type := 
{
  coprod : Ob C -> Ob C -> Ob C;
  coproj1 : forall A B : Ob C, Hom A (coprod A B);
  coproj2 : forall A B : Ob C, Hom B (coprod A B);
  is_coprod : forall A B : Ob C,
    coproduct C (coprod A B) (coproj1 A B) (coproj2 A B)
}.

(*Definition has_finite_products (C : Cat) : Prop :=
    has_terminal_object C /\ has_binary_products C.

Definition has_finite_coproducts (C : Cat) : Prop :=
    has_initial_object C /\ has_binary_coproducts C.*)

Theorem dual_product_coproduct : forall (C : Cat) (A B P : Ob C)
    (pA : Hom P A) (pB : Hom P B), product C P pA pB <->
    coproduct (Dual C) P pA pB.
unfold product, coproduct; split; intros.
unfold Hom, Dual. apply H.
unfold Hom, Dual in H. apply H.
Qed.

Theorem product_comm : forall (C : Cat) (A B : Ob C) (P : Ob C) (pA : Hom P A)
    (pB : Hom P B), product C P pA pB -> product C P pB pA.
unfold product in *; intros.
destruct (H X g f) as (u, [[eq1 eq2] uniq]); clear H.
exists u. split.
(*Case "Universal property".*) split; assumption.
(*Case "Uniquenes".*) intros. apply uniq. destruct H; split; assumption.
Qed.

Theorem coproduct_comm : forall (C : Cat) (A B : Ob C) (P : Ob C) (iA : Hom A P)
    (iB : Hom B P), coproduct C P iA iB -> coproduct C P iB iA.
unfold coproduct in *; intros. destruct (H X g f) as (u, [[eq1 eq2] uniq]).
exists u. split.
(* Universal property *) split; assumption.
(* Uniqueness *) intros. apply uniq. destruct H0; split; assumption.
Qed.
(*Restart.
intro C. rewrite <- (dual_involution C). intros.
rewrite <- (dual_product_coproduct (Dual C)) in *.
apply product_comm. assumption.*)

(*  A weird auxiliary (f : Hom A B) is needed here to instantiate the product
    definition. In case of the big product, this is not needed. *)
Theorem proj_ret : forall (C : Cat) (A B P : Ob C) (pA : Hom P A)
    (pB : Hom P B) (f : Hom A B), product C P pA pB -> Ret pA.
Proof.
  unfold product, Ret in *; intros.
  destruct (H A (id A) f) as (u, [[eq1 eq2] uniq]); clear H.
  exists u. rewrite eq1. reflexivity.
Qed.

(*  The f : Hom B A is auxiliary as in the case of the product. *)
Theorem coproj_sec : forall (C : Cat) (A B P : Ob C) (iA : Hom A P) (iB : Hom B P)
    (f : Hom B A), coproduct C P iA iB -> Sec iA.
Proof.
  unfold Sec, coproduct in *; intros.
  destruct (H A (id A) f) as (u, [[eq1 eq2] uniq]).
  exists u. rewrite eq1. reflexivity.
Qed.
(* The Dual doesn't work
intros C. rewrite <- (dual_involution C). intros.
simpl in iA, iB. rewrite dual_sec_ret.
rewrite <- dual_product_coproduct in H.
apply proj_ret in H; assumption.
Qed.*)

Theorem product_iso_unique : forall (C : Cat) (A B : Ob C) (P : Ob C)
    (pA : Hom P A) (pB : Hom P B) (Q : Ob C) (qA : Hom Q A) (qB : Hom Q B),
    product C P pA pB -> product C Q qA qB -> P ~ Q.
intros.
unfold product, isomorphic in *.
destruct (H0 P pA pB) as (u1, [[iso_pA iso_pB] unique1]);
destruct (H Q qA qB) as (u2, [[iso_qA iso_qB] unique2]).
exists u1. unfold Iso. exists u2. split.
destruct (H P pA pB) as (i, [[i_iso1 i_iso2] uq]).
assert (i_is_id : i == id P). apply uq. cat.
rewrite <- i_is_id.
symmetry. apply uq. split.
cat. rewrite <- iso_qA. assumption.
cat. rewrite <- iso_qB. assumption.
destruct (H0 Q qA qB) as (i, [[i_iso1 i_iso2] uq]).
assert (i_is_id : i == id Q). apply uq. cat.
rewrite <- i_is_id.
symmetry. apply uq. split.
cat. rewrite <- iso_pA. assumption.
cat. rewrite <- iso_pB. assumption.
Qed.

Theorem iso_prod : forall (C' : Cat) (A B C D P Q : Ob C') (pA : Hom P A)
    (pB : Hom P B) (qC : Hom Q C) (qD : Hom Q D),
    A ~ C -> B ~ D -> product C' P pA pB -> product C' Q qC qD -> P ~ Q.
intros.
unfold product, isomorphic in *.
destruct H as (f, [f' [f_iso1 f_iso2]]), H0 as (g, [g' [g_iso1 g_iso2]]).
destruct (H2 P (pA .> f) (pB .> g)) as (u1, [[u1_proj1 u1_proj2] uniq1]).
destruct (H1 Q (qC .> f') (qD .> g')) as (u2, [[u2_proj1 u2_proj2] uniq2]).
exists u1. unfold Iso. exists u2. split.
destruct (H1 P pA pB) as (i, [_ uq]). 
assert (i_is_id : i == id P). apply uq. cat.
rewrite <- i_is_id.
symmetry. apply uq. split.
cat. rewrite <- u2_proj1.
assert (As1 : pA .> f .> f' == u1 .> qC .> f'). rewrite u1_proj1. reflexivity.
rewrite <- comp_assoc. rewrite <- As1. cat. rewrite f_iso1. cat.
cat. rewrite <- u2_proj2.
assert (As2 : pB .> g .> g' == u1 .> qD .> g'). rewrite u1_proj2. reflexivity.
rewrite <- comp_assoc. rewrite <- As2. cat. rewrite g_iso1. cat.
destruct (H2 Q qC qD) as (i, [_ uq]).
assert (i_is_id : i == id Q). apply uq. cat.
rewrite <- i_is_id.
symmetry. apply uq. split.
cat. rewrite <- u1_proj1.
assert (As1 : qC .> f' .> f == u2 .> pA .> f). rewrite u2_proj1. reflexivity.
rewrite <- comp_assoc. rewrite <- As1. cat. rewrite f_iso2. cat.
cat. rewrite <- u1_proj2.
assert (As2 : qD .> g' .> g == u2 .> pB .> g). rewrite u2_proj2. reflexivity.
rewrite <- comp_assoc. rewrite <- As2. cat. rewrite g_iso2. cat.
Qed.

Theorem product_iso_unique2 : forall (C : Cat) (A B : Ob C) (P : Ob C)
    (pA : Hom P A) (pB : Hom P B) (Q : Ob C) (qA : Hom Q A) (qB : Hom Q B),
    product C P pA pB -> product C Q qA qB -> P ~ Q.
Proof.
  intros. eapply iso_prod; eauto; reflexivity.
Qed.

(*
Theorem prod_assoc : forall (_ : Cat) (A B C AB BC A_BC AB_C : Ob C)
    (pAB_A : Hom AB A) (pAB_B : Hom AB B) (pBC_B : Hom BC B) (pBC_C : Hom BC C)
    (pA_BC_A : Hom A_BC A) (pA_BC_BC : Hom A_BC BC) (pAB_C_AB : Hom AB_C AB)
    (pAB_C_C : Hom AB_C C),
    product AB pAB_A pAB_B -> product BC pBC_B pBC_C ->
    product A_BC pA_BC_A pA_BC_BC -> product AB_C pAB_C_AB pAB_C_C ->
    A_BC ~ AB_C.
*)

(*Theorem prod_coprod_distr_uniq : foral (_ : Cat) ( 
*)