Require Export Cat.
Require Export Functor.

Set Universe Polymorphism.

Definition product (C : Cat) {A B : Ob C} (P : Ob C) (p1 : Hom P A)
    (p2 : Hom P B) := forall (X : Ob C) (f : Hom X A) (g : Hom X B),
    exists!! u : Hom X P, f == u .> p1 /\ g == u .> p2.

Definition coproduct (C : Cat) {A B : Ob C} (P : Ob C) (iA : Hom A P)
    (iB : Hom B P) := forall (X : Ob C) (f : Hom A X) (g : Hom B X),
    exists!! u : Hom P X, f == iA .> u /\ g == iB .> u.

Definition biproduct (C : Cat) {A B : Ob C} (P : Ob C) (pA : Hom P A)
    (pB : Hom P B) (iA : Hom A P) (iB : Hom B P) : Prop :=
    product C P pA pB /\ coproduct C P iA iB.
Print setoid_unique.

Definition product_skolem (C : Cat) {A B : Ob C} (P : Ob C)
    (p1 : Hom P A) (p2 : Hom P B)
    (diag : forall {X : Ob C} (f : Hom X A) (g : Hom X B), Hom X P) : Prop :=
    forall (X : Ob C) (f : Hom X A) (g : Hom X B),
    setoid_unique (fun d => f == d .> p1 /\ g == d .> p2) (diag f g).

Definition coproduct_skolem (C : Cat) {A B : Ob C} (P : Ob C)
    (p1 : Hom A P) (p2 : Hom B P)
    (codiag : forall {X : Ob C} (f : Hom A X) (g : Hom B X), Hom P X) : Prop :=
    forall (X : Ob C) (f : Hom A X) (g : Hom B X),
    setoid_unique (fun d => f == p1 .> d /\ g == p2 .> d) (codiag f g).

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
  (* Proper *) cat.
    rewrite H, H0. reflexivity.
    rewrite H1, H2. reflexivity.
  (* Category laws *) all: cat.
Defined.

Class has_prod_functor (C : Cat) : Type :=
{
    prod_functor : Functor (CAT_prod C C) C;
    proj1'' : forall A B : Ob C, Hom (prod_functor (A, B)) A;
    proj2'' : forall A B : Ob C, Hom (prod_functor (A, B)) B;
    is_prod' : forall A B : Ob C,
      product C (@fob (CAT_prod C C) C prod_functor (A, B))
      (proj1'' A B) (proj2'' A B)
}.

Class has_products (C : Cat) : Type :=
{
    prodob : Ob C -> Ob C -> Ob C;
    p1 : forall A B : Ob C, Hom (prodob A B) A;
    p2 : forall A B : Ob C, Hom (prodob A B) B;
    diag : forall (A B X : Ob C) (f : Hom X A) (g : Hom X B),
      Hom X (prodob A B);
    is_product : forall (A B : Ob C),
      product_skolem C (prodob A B) (p1 A B) (p2 A B) (diag A B);
}.

(*Definition fmap_prod {C : Cat} {hp : has_products C} {X X' Y Y' : Ob C}
    (f : Hom X Y) (g : Hom X' Y') : Hom (prodob X X') (prodob Y Y')
  := (@diag C hp _ _ _ (p1 X X' .> f) (p2 X X' .> g)).*)

(* TODO: Fix notations. 
Notation "A × B" := (prod_functor (A, B)) (at level 40).
Notation "f ×' g" := (fmap prod_functor f g) (at level 40). *)

Class has_coproducts (C : Cat) : Type := 
{
    coprod : Ob C -> Ob C -> Ob C;
    coproj1 : forall A B : Ob C, Hom A (coprod A B);
    coproj2 : forall A B : Ob C, Hom B (coprod A B);
    codiag : forall (A B X : Ob C) (f : Hom A X) (g : Hom B X),
      Hom (coprod A B) X;
    is_coprod : forall A B : Ob C,
      coproduct_skolem C (coprod A B) (coproj1 A B) (coproj2 A B) (codiag A B)
}.

Class has_coprod_functor (C : Cat) : Type :=
{
    coprod_functor : Functor (CAT_prod C C) C;
    coproj1' : forall X Y : Ob C, Hom X (coprod_functor (X, Y));
    coproj2' : forall X Y : Ob C, Hom Y (coprod_functor (X, Y));
    codiag' : forall X : Ob C, Hom (coprod_functor (X, X)) X;
    is_coprod' : forall (A B X : Ob C) (f : Hom A X) (g : Hom B X),
        f == coproj1' A B .> @fmap _ _ coprod_functor (A, B) (X, X) (f, g)
        .> codiag' X
        /\
        g == coproj2' A B .> @fmap _ _ coprod_functor (A, B) (X, X) (f, g)
        .> codiag' X
}.

Theorem dual_product_coproduct : forall (C : Cat) (A B P : Ob C)
    (pA : Hom P A) (pB : Hom P B), product C P pA pB <->
    coproduct (Dual C) P pA pB.
Proof.
  unfold product, coproduct; split; intros.
  unfold Hom, Dual. apply H.
  unfold Hom, Dual in H. apply H.
Restart.
  cat.
Qed.

Theorem dual_biproduct_self : forall (C : Cat) (A B P : Ob C)
    (pA : Hom P A) (pB : Hom P B) (iA : Hom A P) (iB : Hom B P),
    biproduct C P pA pB iA iB <-> biproduct (Dual C) P iA iB pA pB.
Proof. unfold biproduct. cat. Qed.

Theorem product_comm : forall (C : Cat) (A B : Ob C) (P : Ob C) (pA : Hom P A)
    (pB : Hom P B), product C P pA pB -> product C P pB pA.
Proof.
  unfold product in *; intros.
  destruct (H X g f) as (u, [[eq1 eq2] uniq]); clear H.
  exists u. split.
    (* Universal property *) split; assumption.
    (* Uniquenes *) intros. apply uniq. destruct H; split; assumption.
Restart.
  unfold product in *; intros. destruct (H X g f); eexists; cat.
Qed.

Theorem coproduct_comm : forall (C : Cat) (A B : Ob C) (P : Ob C) (iA : Hom A P)
    (iB : Hom B P), coproduct C P iA iB -> coproduct C P iB iA.
Proof.
  unfold coproduct; intros. destruct (H X g f). eexists; cat.
Restart. (* Duality! *)
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite <- (dual_product_coproduct (Dual C)) in *.
  apply product_comm. assumption.
Qed.

Hint Resolve product_comm coproduct_comm.

Theorem biprod_comm : forall (C : Cat) (A B : Ob C) (P : Ob C)
    (pA : Hom P A) (pB : Hom P B) (iA : Hom A P) (iB : Hom B P),
    biproduct C P pA pB iA iB -> biproduct C P pB pA iB iA.
Proof. unfold biproduct. cat. Qed.

(*  A weird auxiliary (f : Hom A B) is needed here to instantiate the product
    definition. In case of the big product, this is not needed. *)
Theorem proj_ret : forall (C : Cat) (A B P : Ob C) (pA : Hom P A)
    (pB : Hom P B) (f : Hom A B), product C P pA pB -> Ret pA.
Proof.
  unfold product, Ret; intros.
  edestruct (H A (id A) f) as (u, [[eq1 eq2] uniq]).
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

Theorem product_iso : forall (C' : Cat) (A B C D P Q : Ob C')
    (pA : Hom P A) (pB : Hom P B) (qC : Hom Q C) (qD : Hom Q D),
    A ~ C -> B ~ D -> product C' P pA pB -> product C' Q qC qD -> P ~ Q.
Proof.
  unfold product, isomorphic; intros.
  destruct H as (f, [f' [f_iso1 f_iso2]]), H0 as (g, [g' [g_iso1 g_iso2]]).
  destruct (H2 P (pA .> f) (pB .> g)) as (u1, [[u1_proj1 u1_proj2] uniq1]).
  destruct (H1 Q (qC .> f') (qD .> g')) as (u2, [[u2_proj1 u2_proj2] uniq2]).
  unfold Iso. exists u1, u2. split.
    destruct (H1 P pA pB) as (i, [_ uq]).
      assert (i_is_id : i == id P). apply uq. cat.
      rewrite <- i_is_id. symmetry. apply uq. split.
        cat. rewrite <- u2_proj1.
          assert (As1 : pA .> f .> f' == u1 .> qC .> f').
            rewrite u1_proj1. reflexivity.
          rewrite <- comp_assoc. rewrite <- As1. cat. rewrite f_iso1. cat.
        cat. rewrite <- u2_proj2.
          assert (As2 : pB .> g .> g' == u1 .> qD .> g').
            rewrite u1_proj2. reflexivity.
          rewrite <- comp_assoc. rewrite <- As2. cat. rewrite g_iso1. cat.
    destruct (H2 Q qC qD) as (i, [_ uq]).
      assert (i_is_id : i == id Q). apply uq. cat.
      rewrite <- i_is_id. symmetry. apply uq. split.
        cat. rewrite <- u1_proj1.
          assert (As1 : qC .> f' .> f == u2 .> pA .> f).
            rewrite u2_proj1. reflexivity.
          rewrite <- comp_assoc. rewrite <- As1. cat. rewrite f_iso2. cat.
        cat. rewrite <- u1_proj2.
          assert (As2 : qD .> g' .> g == u2 .> pB .> g).
            rewrite u2_proj2. reflexivity.
          rewrite <- comp_assoc. rewrite <- As2. cat. rewrite g_iso2. cat.
Qed.

Theorem coproduct_iso : forall (C' : Cat) (A B C D P Q : Ob C')
    (iA : Hom A P) (iB : Hom B P) (jC : Hom C Q) (jD : Hom D Q),
    A ~ C -> B ~ D -> coproduct C' P iA iB -> coproduct C' Q jC jD -> P ~ Q.
Proof.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite <- (dual_product_coproduct (Dual C)) in *.
  rewrite dual_isomorphic_self in *.
  eapply product_iso. exact H. exact H0. exact H2. exact H1.
Defined.

Theorem biproduct_iso : forall (C' : Cat) (A B C D P Q : Ob C')
    (pA : Hom P A) (pB : Hom P B) (iA : Hom A P) (iB : Hom B P)
    (qC : Hom Q C) (qD : Hom Q D) (jC : Hom C Q) (jD : Hom D Q),
    A ~ C -> B ~ D ->
    biproduct C' P pA pB iA iB -> biproduct C' Q qC qD jC jD -> P ~ Q.
Proof.
  unfold biproduct. cat.
  apply (product_iso C' A B C D P Q pA pB qC qD H H0 H1 H2).
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