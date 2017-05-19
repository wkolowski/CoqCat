Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.Cat.
Require Export Functor.

Definition product (C : Cat) {A B : Ob C} (P : Ob C) (p1 : Hom P A)
    (p2 : Hom P B) := forall (X : Ob C) (f : Hom X A) (g : Hom X B),
    exists!! u : Hom X P, f == u .> p1 /\ g == u .> p2.

Definition coproduct (C : Cat) {A B : Ob C} (P : Ob C) (iA : Hom A P)
    (iB : Hom B P) := forall (X : Ob C) (f : Hom A X) (g : Hom B X),
    exists!! u : Hom P X, f == iA .> u /\ g == iB .> u.

Definition biproduct (C : Cat) {A B : Ob C} (P : Ob C) (pA : Hom P A)
    (pB : Hom P B) (iA : Hom A P) (iB : Hom B P) : Prop :=
    product C P pA pB /\ coproduct C P iA iB.

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
Defined.

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

(* TODO : dual for coproducts (and one for biproducts too) *)
Theorem iso_to_prod_is_prod : forall (C : Cat) (A B P P' : Ob C)
  (p1 : Hom P A) (p2 : Hom P B), product C P p1 p2 ->
    forall f : Hom P' P, Iso f -> product C P' (f .> p1) (f .> p2).
Proof.
  intros. destruct H0 as [g [eq1 eq2]]. Show Proof.
  unfold product in *. intros.
  destruct (H X f0 g0) as [xp [[xp_eq1 xp_eq2] xp_unique]].
  exists (xp .> g). repeat split.
    rewrite comp_assoc. rewrite <- (comp_assoc g f).
      rewrite eq2. rewrite id_left. assumption.
    rewrite comp_assoc. rewrite <- (comp_assoc g f).
      rewrite eq2. rewrite id_left. assumption.
    intros. do 2 rewrite <- comp_assoc in H0.
      specialize (xp_unique (y .> f) H0). rewrite xp_unique.
      rewrite comp_assoc. rewrite eq1. rewrite id_right. reflexivity.
Qed.

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

Theorem biproduct_comm : forall (C : Cat) (A B : Ob C) (P : Ob C)
    (pA : Hom P A) (pB : Hom P B) (iA : Hom A P) (iB : Hom B P),
    biproduct C P pA pB iA iB -> biproduct C P pB pA iB iA.
Proof. unfold biproduct. cat. Qed.
