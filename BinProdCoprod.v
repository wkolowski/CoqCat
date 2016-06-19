Require Export InitTerm.
Require Export Coq.Setoids.Setoid.

Definition is_product `{C : Cat} {A B : Ob} (P : Ob) (p1 : Hom P A)
    (p2 : Hom P B) := forall (X : Ob) (f : Hom X A) (g : Hom X B),
    exists! u : Hom X P, f = u .> p1 /\ g = u .> p2.

Definition is_coproduct `{C : Cat} {A B : Ob} (P : Ob) (iA : Hom A P)
    (iB : Hom B P) := forall (X : Ob) (f : Hom A X) (g : Hom B X),
    exists! u : Hom P X, f = iA .> u /\ g = iB .> u.

Definition has_binary_products `(C : Cat) : Prop := forall (A B : Ob),
    exists (P : Ob) (pA : Hom P A) (pB : Hom P B), is_product P pA pB.

Definition has_binary_coproducts `(C : Cat) : Prop := forall (A B : Ob),
    exists (P : Ob) (iA : Hom A P) (iB : Hom B P), is_coproduct P iA iB.

(*Definition has_finite_products `(C : Cat) : Prop :=
    has_terminal_object C /\ has_binary_products C.

Definition has_finite_coproducts `(C : Cat) : Prop :=
    has_initial_object C /\ has_binary_coproducts C.*)

Theorem product_comm : forall `(C : Cat) (A B : Ob) (P : Ob) (pA : Hom P A)
    (pB : Hom P B), is_product P pA pB -> is_product P pB pA.
unfold is_product in *; intros.
destruct (H X g f) as (u, [[eq1 eq2] uniq]); clear H.
exists u. split.
Case "Universal property". split; assumption.
Case "Uniquenes". intros. apply uniq. destruct H; split; assumption.
Qed.

Theorem coproduct_comm : forall `(C : Cat) (A B : Ob) (P : Ob) (iA : Hom A P)
    (iB : Hom B P), is_coproduct P iA iB -> is_coproduct P iB iA.
unfold is_coproduct in *; intros. destruct (H X g f) as (u, [[eq1 eq2] uniq]).
exists u. split.
Case "Universal property". split; assumption.
Case "Uniqueness". intros. apply uniq. destruct H0; split; assumption.
Qed.

(*  A weird auxiliary (f : Hom A B) is needed here to instantiate the product
    definition. In case of the big product, this is not needed. *)
Theorem proj_ret : forall `(C : Cat) (A B P : Ob) (pA : Hom P A)
    (pB : Hom P B) (f : Hom A B), is_product P pA pB -> Ret pA.
unfold is_product, Ret in *; intros.
destruct (H A (id A) f) as (u, [[eq1 eq2] uniq]); clear H.
exists u. rewrite eq1. trivial.
Qed.

(*  The f : Hom B A is auxiliary as in the case of the product. *)
Theorem inj_sec : forall `(C : Cat) (A B P : Ob) (iA : Hom A P) (iB : Hom B P)
    (f : Hom B A), is_coproduct P iA iB -> Sec iA.
unfold Sec, is_coproduct in *; intros.
destruct (H A (id A) f) as (u, [[eq1 eq2] uniq]).
exists u. rewrite eq1; trivial.
Qed.

Theorem product_iso_unique : forall `(C : Cat) (A B : Ob) (P : Ob)
    (pA : Hom P A) (pB : Hom P B) (Q : Ob) (qA : Hom Q A) (qB : Hom Q B),
    is_product P pA pB -> is_product Q qA qB -> P ~ Q.
intros.
unfold is_product, isomorphic in *.
destruct (H0 P pA pB) as (u1, [[iso_pA iso_pB] unique1]);
destruct (H Q qA qB) as (u2, [[iso_qA iso_qB] unique2]).
exists u1. unfold Iso. exists u2. split.
destruct (H P pA pB) as (i, [[i_iso1 i_iso2] uq]).
assert (i_is_id : i = id P). apply uq. cat.
rewrite <- i_is_id.
symmetry. apply uq. split.
cat. rewrite <- iso_qA. assumption.
cat. rewrite <- iso_qB. assumption.
destruct (H0 Q qA qB) as (i, [[i_iso1 i_iso2] uq]).
assert (i_is_id : i = id Q). apply uq. cat.
rewrite <- i_is_id.
symmetry. apply uq. split.
cat. rewrite <- iso_pA. assumption.
cat. rewrite <- iso_pB. assumption.
Qed.

Theorem iso_prod : forall `(_ : Cat) (A B C D P Q : Ob) (pA : Hom P A)
    (pB : Hom P B) (qC : Hom Q C) (qD : Hom Q D),
    A ~ C -> B ~ D -> is_product P pA pB -> is_product Q qC qD -> P ~ Q.
intros.
unfold is_product, isomorphic in *.
destruct H0 as (f, [f' [f_iso1 f_iso2]]), H1 as (g, [g' [g_iso1 g_iso2]]).
destruct (H3 P (pA .> f) (pB .> g)) as (u1, [[u1_proj1 u1_proj2] uniq1]).
destruct (H2 Q (qC .> f') (qD .> g')) as (u2, [[u2_proj1 u2_proj2] uniq2]).
exists u1. unfold Iso. exists u2. split.
destruct (H2 P pA pB) as (i, [_ uq]). 
assert (i_is_id : i = id P). apply uq. cat.
rewrite <- i_is_id.
symmetry. apply uq. split.
cat. rewrite <- u2_proj1.
assert (As1 : pA .> f .> f' = u1 .> qC .> f'). rewrite u1_proj1. trivial.
rewrite <- comp_assoc. rewrite <- As1. cat. rewrite f_iso1. cat.
cat. rewrite <- u2_proj2.
assert (As2 : pB .> g .> g' = u1 .> qD .> g'). rewrite u1_proj2. trivial.
rewrite <- comp_assoc. rewrite <- As2. cat. rewrite g_iso1. cat.
destruct (H3 Q qC qD) as (i, [_ uq]).
assert (i_is_id : i = id Q). apply uq. cat.
rewrite <- i_is_id.
symmetry. apply uq. split.
cat. rewrite <- u1_proj1.
assert (As1 : qC .> f' .> f = u2 .> pA .> f). rewrite u2_proj1. trivial.
rewrite <- comp_assoc. rewrite <- As1. cat. rewrite f_iso2. cat.
cat. rewrite <- u1_proj2.
assert (As2 : qD .> g' .> g = u2 .> pB .> g). rewrite u2_proj2. trivial.
rewrite <- comp_assoc. rewrite <- As2. cat. rewrite g_iso2. cat.
Qed.

Theorem product_iso_unique2 : forall `(C : Cat) (A B : Ob) (P : Ob)
    (pA : Hom P A) (pB : Hom P B) (Q : Ob) (qA : Hom Q A) (qB : Hom Q B),
    is_product P pA pB -> is_product Q qA qB -> P ~ Q.
intros. apply iso_prod with A B A B pA pB qA qB; try reflexivity; assumption.
Qed.

Theorem prod_assoc : forall `(_ : Cat) (A B C AB BC A_BC AB_C : Ob)
    (pAB_A : Hom AB A) (pAB_B : Hom AB B) (pBC_B : Hom BC B) (pBC_C : Hom BC C)
    (pA_BC_A : Hom A_BC A) (pA_BC_BC : Hom A_BC BC) (pAB_C_AB : Hom AB_C AB)
    (pAB_C_C : Hom AB_C C),
    is_product AB pAB_A pAB_B -> is_product BC pBC_B pBC_C ->
    is_product A_BC pA_BC_A pA_BC_BC -> is_product AB_C pAB_C_AB pAB_C_C ->
    A_BC ~ AB_C.
