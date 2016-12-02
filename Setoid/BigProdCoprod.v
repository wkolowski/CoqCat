Require Export Cat.
Require Export BinProdCoprod.

Set Universe Polymorphism.

Definition big_product {C : Cat} {J : Set} {A : J -> Ob C} (P : Ob C)
    (p : forall j : J, Hom P (A j)) : Prop := forall (X : Ob C) (j : J)
    (f : Hom X (A j)), exists!! u : Hom X P, f == u .> p j.

Definition big_coproduct {C : Cat} {J : Set} {A : J -> Ob C} (P : Ob C)
    (i : forall j : J, Hom (A j) P) := forall (X : Ob C) (j : J)
    (f : Hom (A j) X), exists!! u : Hom P X, f == i j .> u.

Theorem big_proj_ret : forall (C : Cat) (J : Set) (A : J -> Ob C)
    (P : Ob C) (p : forall j : J, Hom P (A j)),
    big_product P p -> forall j : J, Ret (p j).
Proof.
  unfold big_product, Ret; intros.
  destruct (H (A j) j (id (A j))) as (u, [eq uniq]).
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

Class has_all_products (C : Cat) : Type :=
{
    bigProd : forall J : Set, (J -> Ob C) -> Ob C;
    bigProj : forall (J : Set) (A : J -> Ob C) (j : J),
        Hom (bigProd J A) (A j);
    is_big_product : forall (J : Set) (A : J -> Ob C),
        big_product (bigProd J A) (bigProj J A)
}.

(*  The dummy variable j here is needed to make sure J is inhabited. Otherwise
    this theorem degenerates to the empty case. *)
Theorem big_product_iso_unique : forall (C : Cat) (J : Set) (A : J -> Ob C)
    (P Q : Ob C) (p : forall j : J, Hom P (A j))
    (q : forall j : J, Hom Q (A j)) (j : J),
    big_product P p -> big_product Q q -> P ~ Q.
Proof.
  unfold big_product; intros.
  unfold isomorphic. destruct (H0 P j (p j)) as [u1 [eq1 uniq1]],
  (H Q j (q j)) as [u2 [eq2 uniq2]].
  exists u1. unfold Iso. exists u2. split.
    destruct (H P j (p j)) as [i [eq_id uniq_id]].
      assert (i_is_id : i == id P). apply uniq_id. cat.
      rewrite <- i_is_id. symmetry. apply uniq_id. rewrite comp_assoc.
      rewrite <- eq2. assumption.
    destruct (H0 Q j (q j)) as [i [eq_id uniq_id]].
      assert (i_is_id : i == id Q). apply uniq_id. cat.
      rewrite <- i_is_id. symmetry. apply uniq_id. rewrite comp_assoc.
      rewrite <- eq1. assumption.
Qed.

Theorem big_product_iso_unique2 : forall (C : Cat) (J : Set) (A B : J -> Ob C)
    (P Q : Ob C) (p : forall j : J, Hom P (A j)) (q : forall j : J, Hom Q (B j))
    (j : J), (forall j : J, A j ~ B j) ->
    big_product P p -> big_product Q q -> P ~ Q.
unfold big_product; intros.
destruct (H j) as [f [g [iso1 iso2]]].
unfold isomorphic. destruct (H1 P j (p j .> f)) as [u1 [eq1 uniq1]],
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
Qed.

Theorem big_product_iso_unique' : forall (C : Cat) (J : Set) (A : J -> Ob C)
    (P Q : Ob C) (p : forall j : J, Hom P (A j)) (q : forall j : J, Hom Q (A j))
    (j : J), big_product P p -> big_product Q q -> P ~ Q.
intros.
apply big_product_iso_unique2 with J A A p q; try reflexivity; assumption.
Qed.

(*  This probably won't work, because we don't have enough morphisms to
    instantiate the definition of the product. *)
(*Theorem small_and_big_products : forall (C : Cat) (A B P : Ob C) (pA : Hom P A)
    (pB : Hom P B), is_product P pA pB <-> exists (f : bool -> Ob C)
    (p : forall b : bool, Hom P (f b)),
    f true = A /\ f false = B /\ big_product P p.
unfold is_product, big_product; split; intros.
assert (H' : exists f : bool -> Ob C, f true = A /\ f false = B).
exists (fix f (b : bool) := if b then A else B). split; trivial.
destruct H' as [f [eq1 eq2]].
exists f.
assert (p : forall b : bool, Hom P (f b)). destruct b.
rewrite eq1. exact pA. rewrite eq2. exact pB.
exists p. split; try split; try assumption. intros.
assert (pA' : Hom P A). rewrite <- eq1. apply (p true).
assert (pB' : Hom P B). rewrite <- eq2. apply (p false).
destruct j.*)

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

Theorem unary_prod_exists : forall (C : Cat) (A : unit -> Ob C),
    big_product (A tt) (fun _ : unit => id (A tt)).
Proof.
  unfold big_product; intros. exists f; split; intros; cat.
Restart.
  red. eexists. cat.
Qed.

Theorem unary_coprod_exists : forall (C : Cat) (A : unit -> Ob C),
    big_coproduct (A tt) (fun _ : unit => id (A tt)).
Proof.
  unfold big_coproduct; intros. exists f; split; intros; cat.
Restart.
  red. eexists. cat.
Qed.

(* WARNING: ANY OBJECT IS NULLARY PRODUCT *)
Theorem nullary_prod : forall (C : Cat) (A : Empty_set -> Ob C) (T : Ob C)
    (p : forall j : Empty_set, Hom T (A j)),
    (*terminal_object T ->*) big_product T p.
Proof.
  unfold big_product. inversion j.
Qed.
