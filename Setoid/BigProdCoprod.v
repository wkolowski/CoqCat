Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Set Universe Polymorphism.

Definition big_product {C : Cat} {J : Set} {A : J -> Ob C} (P : Ob C)
    (p : forall j : J, Hom P (A j)) : Prop := forall (X : Ob C)
    (f : forall j : J, Hom X (A j)),
    exists!! u : Hom X P, forall j : J, f j == u .> p j.

Definition big_coproduct {C : Cat} {J : Set} {A : J -> Ob C} (P : Ob C)
    (i : forall j : J, Hom (A j) P) : Prop := forall (X : Ob C)
    (f : forall j : J, Hom (A j) X),
    exists!! u : Hom P X, forall j : J, f j == i j .> u.

Definition big_biproduct {C : Cat} {J : Set} {A : J -> Ob C} (P : Ob C)
    (proj : forall j : J, Hom P (A j))
    (coproj : forall j : J, Hom (A j) P) : Prop :=
        big_product P proj /\ big_coproduct P coproj.

(*Theorem big_proj_ret : forall (C : Cat) (J : Set) (A : J -> Ob C)
    (P : Ob C) (p : forall j : J, Hom P (A j)),
    big_product P p -> forall j : J, Ret (p j).
Proof.
  unfold big_product, Ret; intros.
  destruct (H (A j) (fun j' : J => id (A j))) as (u, [eq uniq]).
  exists u. rewrite eq. reflexivity.
Qed.

Theorem big_inj_sec : forall (C : Cat) (J : Set) (A : J -> Ob C)
    (P : Ob C) (i : forall j : J, Hom (A j) P),
    big_coproduct P i -> forall j : J, Sec (i j).
Proof.
  unfold big_coproduct, Sec in *; intros.
  destruct (H (A j) j (id (A j))) as (u, [eq uniq]); clear H.
  exists u. rewrite <- eq. reflexivity.
Qed.
*)

Class has_all_products (C : Cat) : Type :=
{
    bigProd : forall J : Set, (J -> Ob C) -> Ob C;
    bigProj : forall (J : Set) (A : J -> Ob C) (j : J),
        Hom (bigProd J A) (A j);
    is_big_product : forall (J : Set) (A : J -> Ob C),
        big_product (bigProd J A) (bigProj J A)
}.

Class has_all_coproducts (C : Cat) : Type :=
{
    bigCoprod : forall J : Set, (J -> Ob C) -> Ob C;
    bigCoproj : forall (J : Set) (A : J -> Ob C) (j : J),
        Hom (A j) (bigCoprod J A);
    is_big_coproduct : forall (J : Set) (A : J -> Ob C),
        big_coproduct (bigCoprod J A) (bigCoproj J A)
}.

Class has_all_biproducts (C : Cat) : Type :=
{
    bigProduct :> has_all_products C;
    bigCoproduct :> has_all_coproducts C;
    product_is_coproduct : forall (J : Set) (A : J -> Ob C),
        bigProd J A = bigCoprod J A
}.

Theorem big_product_iso_unique : forall (C : Cat) (J : Set) (A : J -> Ob C)
    (P Q : Ob C) (p : forall j : J, Hom P (A j))
    (q : forall j : J, Hom Q (A j)),
    big_product P p -> big_product Q q -> P ~ Q.
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

(*Theorem big_product_iso_unique2 : forall (C : Cat) (J : Set)
    (A B : J -> Ob C) (P Q : Ob C)
    (p : forall j : J, Hom P (A j)) (q : forall j : J, Hom Q (B j)),
    (forall j : J, A j ~ B j) ->
    big_product P p -> big_product Q q -> P ~ Q.
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

(*Theorem big_product_iso_unique' : forall (C : Cat) (J : Set) (A : J -> Ob C)
    (P Q : Ob C) (p : forall j : J, Hom P (A j)) (q : forall j : J, Hom Q (A j))
    (j : J), big_product P p -> big_product Q q -> P ~ Q.
intros.
apply big_product_iso_unique2 with J A A p q; try reflexivity; assumption.
Qed.*)

Program Theorem small_and_big_products : forall (C : Cat) (A B P : Ob C) (pA : Hom P A)
    (pB : Hom P B), product C P pA pB <-> exists (f : bool -> Ob C)
    (p : forall b : bool, Hom P (f b)),
    f true = A /\ f false = B /\ big_product P p.
Proof.
  unfold product, big_product; simpl; split; intros.

(*    exists (fun b : bool => if b then A else B).
    assert (p : {f : forall b : bool, Hom P (if b then A else B) |
      f true = pA /\ f false = pB}).
      exists (fun b : bool => if b then pA else pA).
    exists p. repeat split; auto; intros.
      destruct (H X (f true) (f false)) as [u [[eq1 eq2] unique]].
      exists u. split; intros. destruct j.
*)

(*    assert (H' : exists f : bool -> Ob C, f true = A /\ f false = B).
      exists (fix f (b : bool) := if b then A else B). auto.
    destruct H' as [f [eq1 eq2]]. exists f.
      assert (p : forall b : bool, Hom P (f b)). destruct b.
        rewrite eq1. exact pA.
        rewrite eq2. exact pB.
      exists p. split; try split; try assumption. intros.
        assert (fXA : Hom X A). rewrite <- eq1. apply (f0 true).
        assert (fXB : Hom X B). rewrite <- eq2. apply (f0 false).
        destruct (H X fXA fXB) as [u [[u_eq1 u_eq2] u_unique]].
        exists u. red. split; intros. destruct j.
          auto.

*)
Abort.

(*Theorem big_product_comm : forall (C : Cat) (J : Set) (A : J -> Ob C) (P : Ob C)
    (f : J -> J) (p : forall j : J, Hom P (A j))
    (p' : forall j : J, Hom P (A (f j))),
    bijective f -> big_product P p -> big_product P p'.
unfold bijective, injective, surjective, big_product; intros.
destruct H as [inj sur].
assert (H' : exists j' : J, f j' = j). apply sur.
destruct H' as (j', proof).
destruct (H0 X (f j') f0).
*)

Theorem nullary_prod : forall (C : Cat) (A : Empty_set -> Ob C) (T : Ob C)
    (p : forall j : Empty_set, Hom T (A j)),
    terminal T -> big_product T p.
Proof.
  unfold big_product, terminal; intros.
  destruct (H X) as [u [_ unique]]. exists u. cat.
Qed.

Theorem nullary_coprod : forall (C : Cat) (A : Empty_set -> Ob C) (I : Ob C)
    (p : forall j : Empty_set, Hom (A j) I),
    initial I -> big_coproduct I p.
Proof.
  unfold big_coproduct, initial; intros.
  edestruct H. eexists. cat.
Qed.

Theorem unary_prod_exists : forall (C : Cat) (A : unit -> Ob C),
    big_product (A tt) (fun _ : unit => id (A tt)).
Proof.
  unfold big_product; intros. exists (f tt). cat.
Qed.

Theorem unary_coprod_exists : forall (C : Cat) (A : unit -> Ob C),
    big_coproduct (A tt) (fun _ : unit => id (A tt)).
Proof.
  unfold big_coproduct; intros. exists (f tt). cat.
Qed.

