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
      : Prop := forall (X : Ob C) (f : forall j : J, Hom X (A j)) (j : J), 
        setoid_unique (fun d : Hom X P => forall j : J, f j == d .> proj j)
          (diag X f).

Definition big_coproduct_skolem (C : Cat) {J : Set} {A : J -> Ob C} (P : Ob C)
    (coproj : forall j : J, Hom (A j) P)
    (codiag : forall (X : Ob C) (f : forall j : J, Hom (A j) X), Hom P X)
      : Prop := forall (X : Ob C) (f : forall j : J, Hom (A j) X) (j : J), 
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

(* Error: Case analysis on sort Type is not allowed for inductive definition ex.
Theorem big_product_iso_unique2 : forall (C : Cat) (J : Set)
    (A B : J -> Ob C) (P Q : Ob C)
    (p : forall j : J, Hom P (A j)) (q : forall j : J, Hom Q (B j)),
    (forall j : J, A j ~ B j) ->
    big_product C P p -> big_product C Q q -> P ~ Q.
Proof.
  unfold big_product; intros.
  assert (f : forall j : J, Hom P (A j)).
    intro. destruct (H j) as [f [g [iso1 iso2]]].
unfold isomorphic. destruct (H1 P (fun j => p j .> H j)) as [u1 [eq1 uniq1]],
(H0 Q j (q j .> g)) as [u2 [eq2 uniq2]].
exists u1. unfold Iso. exists u2. split.
destruct (H0 P j (p j)) as [i [eq_id uniq_id]].
assert (i_is_id : i == id P). apply uniq_id. cat.
rewrite <- i_is_id. symmetry. apply uniq_id. rewrite comp_assoc.
rewrite <- eq2. rewrite <- comp_assoc. rewrite <- eq1. cat.
rewrite iso1. cat.
destruct (H1 Q j (q j)) as [i [eq_id uniq_id]].
assert (i_is_id : i == id Q). apply uniq_id. cat.
rewrite <- i_is_id. symmetry. apply uniq_id. rewrite comp_assoc.
rewrite <- eq1. rewrite <- comp_assoc. rewrite <- eq2. cat.
rewrite iso2. cat.
Qed.*)

Theorem small_and_big_products : forall (C : Cat) (A B P : Ob C)
    (pA : Hom P A) (pB : Hom P B), product C P pA pB <->
    exists (f : bool -> Ob C) (p : forall b : bool, Hom P (f b)),
    f true = A /\ f false = B /\ big_product C P p.
Proof.
  (* Hard and buggy *)
Abort.

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

(* Case analysis on sort Prop bla bla...
Theorem big_product_comm : forall (C : Cat) (J : Set) (A : J -> Ob C) (P : Ob C)
    (f : J -> J) (p : forall j : J, Hom P (A j))
    (p' : forall j : J, Hom P (A (f j))),
    bijective f -> big_product C P p -> big_product C P p'.
Proof.
  unfold bijective, injective, surjective, big_product; intros.
  destruct H as [inj sur].
  assert (forall j : J, Hom X (A j)).
    intro.
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