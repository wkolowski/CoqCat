Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Definition big_product (C : Cat) {J : Set} {A : J -> Ob C} (P : Ob C)
    (p : forall j : J, Hom P (A j)) : Prop := forall (X : Ob C)
    (f : forall j : J, Hom X (A j)),
    exists!! u : Hom X P, forall j : J, f j == u .> p j.

Definition big_coproduct (C : Cat) {J : Set} {A : J -> Ob C} (P : Ob C)
    (i : forall j : J, Hom (A j) P) : Prop := forall (X : Ob C)
    (f : forall j : J, Hom (A j) X),
    exists!! u : Hom P X, forall j : J, f j == i j .> u.

Definition big_biproduct (C : Cat) {J : Set} {A : J -> Ob C} (P : Ob C)
    (proj : forall j : J, Hom P (A j))
    (coproj : forall j : J, Hom (A j) P) : Prop :=
        big_product C P proj /\ big_coproduct C P coproj.

Definition big_product_skolem (C : Cat) {J : Set} {A : J -> Ob C} (P : Ob C)
    (proj : forall j : J, Hom P (A j))
    (diag : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P)
      : Prop := forall (X : Ob C) (f : forall j : J, Hom X (A j)), 
        setoid_unique (fun d : Hom X P => forall j : J, f j == d .> proj j)
          (diag X f).

Definition big_coproduct_skolem (C : Cat) {J : Set} {A : J -> Ob C} (P : Ob C)
    (coproj : forall j : J, Hom (A j) P)
    (codiag : forall (X : Ob C) (f : forall j : J, Hom (A j) X), Hom P X)
      : Prop := forall (X : Ob C) (f : forall j : J, Hom (A j) X), 
        setoid_unique (fun d : Hom P X => forall j : J, f j == coproj j .> d)
          (codiag X f).

Definition big_biproduct_skolem (C : Cat) {J : Set} {A : J -> Ob C} (P : Ob C)
    (proj : forall j : J, Hom P (A j)) (coproj : forall j : J, Hom (A j) P)
    (diag : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P)
    (codiag : forall (X : Ob C) (f : forall j : J, Hom (A j) X), Hom P X)
    : Prop :=
      big_product_skolem C P proj diag /\
      big_coproduct_skolem C P coproj codiag.

Theorem big_product_iso_unique : forall (C : Cat) (J : Set) (A : J -> Ob C)
    (P Q : Ob C) (p : forall j : J, Hom P (A j))
    (q : forall j : J, Hom Q (A j)),
    big_product C P p -> big_product C Q q -> P ~ Q.
Proof.
  unfold big_product; intros.
  unfold isomorphic. destruct (H0 P p) as [u1 [eq1 uniq1]],
  (H Q q) as [u2 [eq2 uniq2]].
  exists u1. unfold Iso. exists u2. split.
    destruct (H P p) as [i [eq_id uniq_id]].
      assert (i_is_id : i == id P). apply uniq_id. cat.
      rewrite <- i_is_id. symmetry. apply uniq_id. intro.
      rewrite comp_assoc. rewrite <- eq2. auto.
    destruct (H0 Q q) as [i [eq_id uniq_id]].
      assert (i_is_id : i == id Q). apply uniq_id. cat.
      rewrite <- i_is_id. symmetry. apply uniq_id. intro.
      rewrite comp_assoc. rewrite <- eq1. auto.
Qed.

Theorem big_product_iso_unique2 : forall (C : Cat) (J : Set)
    (A B : J -> Ob C) (P Q : Ob C)
    (p : forall j : J, Hom P (A j)) (q : forall j : J, Hom Q (B j)),
    (forall j : J, A j ~ B j) ->
    big_product C P p -> big_product C Q q -> P ~ Q.
Proof.
  unfold big_product; intros. red in H.
  assert (f : forall j : J, {f : Hom (A j) (B j) &
    {g : Hom (B j) (A j) | f .> g == id (A j) /\ g .> f == id (B j)}}).
    intro. specialize (H j). apply constructive_indefinite_description in H.
    destruct H as [f f_iso]. exists f.
    red in f_iso. apply constructive_indefinite_description in f_iso.
    destruct f_iso as [g [eq1 eq2]]. exists g. auto.
  assert (f' : {f : forall j : J, Hom (A j) (B j) &
    {g : forall j : J, Hom (B j) (A j) |
      (forall j : J, f j .> g j == id (A j)) /\
      (forall j : J, g j .> f j == id (B j))}}).
    exists (fun j : J => projT1 (f j)).
    exists (fun j : J => proj1_sig (projT2 (f j))).
    split; intro; destruct (f j) as [f' [g' [eq1 eq2]]]; cat.
  destruct f' as [f' [g' [iso1 iso2]]].
  red. destruct (H1 P (fun j => p j .> f' j)) as [u1 [eq1 uniq1]],
    (H0 Q (fun j : J => (q j .> g' j))) as [u2 [eq2 uniq2]].
  exists u1. red. exists u2. split.
    destruct (H0 P (fun j : J => (p j))) as [i [eq_id uniq_id]].
      assert (i_is_id : i == id P). apply uniq_id. cat.
      rewrite <- i_is_id. symmetry. apply uniq_id. intro. cat.
      rewrite <- eq2. rewrite <- comp_assoc. rewrite <- eq1. cat.
      rewrite iso1. cat.
    destruct (H1 Q (fun j : J => q j)) as [i [eq_id uniq_id]].
      assert (i_is_id : i == id Q). apply uniq_id. cat.
      rewrite <- i_is_id. symmetry. apply uniq_id. cat.
      rewrite <- eq1. rewrite <- comp_assoc. rewrite <- eq2. cat.
      rewrite iso2. cat.
Defined.

(* Hard and buggy
Theorem small_and_big_products : forall (C : Cat) (A B P : Ob C)
    (pA : Hom P A) (pB : Hom P B), product C P pA pB <->
    exists (f : bool -> Ob C) (p : forall b : bool, Hom P (f b)),
    f true = A /\ f false = B /\ big_product C P p.
Proof. *)

Theorem nullary_prod : forall (C : Cat) (A : Empty_set -> Ob C) (T : Ob C)
    (p : forall j : Empty_set, Hom T (A j)),
    terminal T -> big_product C T p.
Proof.
  unfold big_product, terminal; intros.
  destruct (H X) as [u [_ unique]]. exists u. cat.
Qed.

Theorem nullary_coprod : forall (C : Cat) (A : Empty_set -> Ob C) (I : Ob C)
    (p : forall j : Empty_set, Hom (A j) I),
    initial I -> big_coproduct C I p.
Proof.
  unfold big_coproduct, initial; intros.
  edestruct H. eexists. cat.
Qed.

Theorem unary_prod_exists : forall (C : Cat) (A : unit -> Ob C),
    big_product C (A tt) (fun _ : unit => id (A tt)).
Proof.
  unfold big_product; intros. exists (f tt). cat.
Qed.

Theorem unary_coprod_exists : forall (C : Cat) (A : unit -> Ob C),
    big_coproduct C (A tt) (fun _ : unit => id (A tt)).
Proof.
  unfold big_coproduct; intros. exists (f tt). cat.
Qed.

(* Dependent type bullshit. This is harder than I thought.
Theorem big_product_comm : forall (C : Cat) (J : Set) (A : J -> Ob C)
    (P : Ob C) (f : J -> J) (p : forall j : J, Hom P (A j))
    (p' : forall j : J, Hom P (A (f j))),
    (forall j : J, p' j = p (f j)) ->
    bijective f -> big_product C P p -> big_product C P p'.
Proof.
  unfold bijective, injective, surjective, big_product.
  destruct 2 as [inj sur]; intros.
  assert (g : {g : J -> J |
    (forall j : J, f (g j) = j) /\ (forall j : J, g (f j) = j)}).
    exists (fun j : J => proj1_sig (constructive_indefinite_description _ (sur j))).
    split; intros.
      destruct (constructive_indefinite_description _ (sur j)). auto.
      destruct (constructive_indefinite_description _ (sur (f j))). auto.
  destruct g as [g [g_inv1 g_inv2]].
(*  assert (h : forall j : J, {h : Hom X (A j) |
  JMeq h (f0 (g j))}).
    intro. pose (h := f0 (g j)). rewrite (g_inv1 j) in h.
    exists h.*)
  assert (h : {h : forall j : J, Hom X (A (f (g j))) |
  (forall j : J, h j = f0 (g j))}).
    exists (fun j : J => f0 (g j)). auto.
  destruct h as [h eq].
  specialize (H0 X h).
  assert (h' : {h' : forall j : J, Hom X (A j) |
    forall j : J, JMeq (h' j) (h j)}).
    exists (fun j : J => h j). intro. rewrite <- (g_inv1 j). exact (h j).
  destruct (H0 X h') as [u H']. exists u. cat. rewrite H.
*)

Class has_all_products (C : Cat) : Type :=
{
    bigProdOb : forall J : Set, (J -> Ob C) -> Ob C;
    bigProj : forall (J : Set) (A : J -> Ob C) (j : J),
        Hom (bigProdOb J A) (A j);
    bigDiag : forall (J : Set) (A : J -> Ob C) (X : Ob C)
      (f : forall j : J, Hom X (A j)), Hom X (bigProdOb J A);
    bigDiag_Proper : forall (J : Set) (A : J -> Ob C) (X : Ob C)
      (f : forall j : J, Hom X (A j)) (g : forall j : J, Hom X (A j)),
      (forall j : J, f j == g j) -> bigDiag J A X f == bigDiag J A X g;
    is_big_product : forall (J : Set) (A : J -> Ob C),
        big_product_skolem C (bigProdOb J A) (bigProj J A) (bigDiag J A)
}.

Class has_all_coproducts (C : Cat) : Type :=
{
    bigCoprodOb : forall J : Set, (J -> Ob C) -> Ob C;
    bigCoproj : forall (J : Set) (A : J -> Ob C) (j : J),
        Hom (A j) (bigCoprodOb J A);
    bigCodiag : forall (J : Set) (A : J -> Ob C) (X : Ob C)
      (f : forall j : J, Hom (A j) X), Hom (bigCoprodOb J A) X;
    bigCodiag_Proper : forall (J : Set) (A : J -> Ob C) (X : Ob C)
      (f : forall j : J, Hom (A j) X) (g : forall j : J, Hom (A j) X),
      (forall j : J, f j == g j) -> bigCodiag J A X f == bigCodiag J A X g;
    is_big_coproduct : forall (J : Set) (A : J -> Ob C),
        big_coproduct_skolem C (bigCoprodOb J A) (bigCoproj J A) (bigCodiag J A)
}.

Class has_all_biproducts (C : Cat) : Type :=
{
    bigProduct :> has_all_products C;
    bigCoproduct :> has_all_coproducts C;
    product_is_coproduct : forall (J : Set) (A : J -> Ob C),
        bigProdOb J A = bigCoprodOb J A
}.