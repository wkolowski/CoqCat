From Cat Require Import Cat.
From Cat.Limits Require Import InitTerm ProdCoprod.

Definition indexed_product
  (C : Cat) {J : Set} {A : J -> Ob C}
  (P : Ob C) (proj : forall j : J, Hom P (A j))
  (tuple : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P)
  : Prop :=
    forall (X : Ob C) (f : forall j : J, Hom X (A j)) (h : Hom X P),
      tuple _ f == h <-> forall j : J, f j == h .> proj j.

Definition indexed_coproduct
  (C : Cat) {J : Set} {A : J -> Ob C}
  (P : Ob C) (coproj : forall j : J, Hom (A j) P)
  (cotuple : forall (X : Ob C) (f : forall j : J, Hom (A j) X), Hom P X)
  : Prop :=
    forall (X : Ob C) (f : forall j : J, Hom (A j) X) (h : Hom P X),
      cotuple _ f == h <-> forall j : J, f j == coproj j .> h.

Class HasIndexedProducts (C : Cat) : Type :=
{
  indexedProdOb :
    forall J : Set, (J -> Ob C) -> Ob C;
  indexedProj :
    forall (J : Set) (A : J -> Ob C) (j : J),
      Hom (indexedProdOb J A) (A j);
  tuple :
    forall (J : Set) (A : J -> Ob C) (X : Ob C) (f : forall j : J, Hom X (A j)),
      Hom X (indexedProdOb J A);
  Proper_tuple :
    forall
      (J : Set) (A : J -> Ob C) (X : Ob C)
      (f : forall j : J, Hom X (A j)) (g : forall j : J, Hom X (A j)),
        (forall j : J, f j == g j) -> tuple J A X f == tuple J A X g;
  is_indexed_product :
    forall (J : Set) (A : J -> Ob C),
      indexed_product C (indexedProdOb J A) (indexedProj J A) (tuple J A)
}.

Arguments indexedProdOb [C _ J] _.
Arguments indexedProj   [C _ J A] _.
Arguments tuple         [C _ J A X] _.

Section HasIndexedProducts.

Context
  [C : Cat]
  [hp : HasIndexedProducts C].

Lemma tuple_indexedProj :
  forall (X : Ob C) (J : Set) (Y : J -> Ob C) (f : forall j : J, Hom X (Y j)) (j : J),
    tuple f .> indexedProj j == f j.
Proof.
  intros; destruct (is_indexed_product _ Y _ f (tuple f)) as [-> _]; reflexivity.
Qed.

Lemma tuple_pre :
  forall (X Y : Ob C) (J : Set) (Z : J -> Ob C) (f : Hom X Y) (g : forall j : J, Hom Y (Z j)),
    f .> tuple g == tuple (fun j : J => f .> g j).
Proof.
  intros.
  symmetry.
  apply is_indexed_product.
  intros.
  rewrite comp_assoc, tuple_indexedProj.
  reflexivity.
Qed.

Lemma tuple_id :
  forall (J : Set) (X : J -> Ob C),
    tuple (@indexedProj C hp J X) == id (indexedProdOb X).
Proof.
  intros.
  apply is_indexed_product.
  intros.
  rewrite comp_id_l.
  reflexivity.
Qed.

Lemma tuple_comp :
  forall
    (J : Set) (X : Ob C) (Y Y' : J -> Ob C)
    (f : forall j : J, Hom X (Y j)) (g : forall j : J, Hom (Y j) (Y' j)),
      tuple (fun j : J => f j .> g j) == tuple f .> tuple (fun j : J => indexedProj j .> g j).
Proof.
  intros.
  apply is_indexed_product; intros.
  rewrite comp_assoc, tuple_indexedProj, <- comp_assoc, tuple_indexedProj.
  reflexivity.
Qed.

End HasIndexedProducts.

Lemma indexed_product_iso_unique :
  forall
    (C : Cat) (J : Set) (A : J -> Ob C)
    (P : Ob C) (p : forall j : J, Hom P (A j))
    (tuple : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P)
    (Q : Ob C) (q : forall j : J, Hom Q (A j))
    (tuple' : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X Q),
      indexed_product C P p tuple -> indexed_product C Q q tuple' -> P ~ Q.
Proof.
  unfold indexed_product, isomorphic, isIso.
  intros.
  exists (tuple' _ p), (tuple0 _ q).
  destruct
    (H P p (tuple' P p .> tuple0 Q q)) as [_ HP2],
    (H Q q (tuple0 Q q)) as [HQ1 _],
    (H0 P p (tuple' P p)) as [HP1' _],
    (H0 Q q (tuple0 Q q .> tuple' P p)) as [_ HQ2'].
  rewrite <- HP2, <- HQ2'; intros.
  - rewrite (H P p (id P)), (H0 Q q (id Q)). cat.
  - rewrite comp_assoc, <- HP1', <- HQ1; cat.
  - rewrite comp_assoc, <- HQ1, <- HP1'; cat.
Defined.

Lemma indexed_product_iso_unique2 :
  forall
    (C : Cat) (J : Set) (A B : J -> Ob C)
    (P1 : Ob C) (p1 : forall j : J, Hom P1 (A j))
    (t1 : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P1)
    (P2 : Ob C) (p2 : forall j : J, Hom P2 (B j))
    (t2 : forall (X : Ob C) (f : forall j : J, Hom X (B j)), Hom X P2),
      (forall j : J, A j ~ B j) ->
      indexed_product C P1 p1 t1 -> indexed_product C P2 p2 t2 -> P1 ~ P2.
Proof.
  unfold indexed_product, isomorphic, isIso.
  intros.
  assert (f : forall j : J, {f : Hom (A j) (B j) &
    {g : Hom (B j) (A j) | f .> g == id (A j) /\ g .> f == id (B j)}}).
  {
    intro. specialize (H j). apply constructive_indefinite_description in H.
    destruct H as [f f_iso]. exists f.
    apply constructive_indefinite_description in f_iso.
    destruct f_iso as [g [eq1 eq2]]. exists g. auto.
  }
  assert (f' : {f : forall j : J, Hom (A j) (B j) &
    {g : forall j : J, Hom (B j) (A j) |
      (forall j : J, f j .> g j == id (A j)) /\
      (forall j : J, g j .> f j == id (B j))}}).
  {
    exists (fun j : J => projT1 (f j)).
    exists (fun j : J => proj1_sig (projT2 (f j))).
    split; intro; destruct (f j) as [f' [g' [eq1 eq2]]]; cat.
  }
  destruct f' as [f' [g' [iso1 iso2]]].
  exists (t2 P1 (fun j => p1 j .> f' j)),
         (t1 P2 (fun j : J => (p2 j .> g' j))).
  split.
  - destruct (H0 P1 p1 (id P1)) as [_ <-]; [| cat].
    symmetry. apply H0. intros. rewrite comp_assoc.
    destruct (H0 P2 (fun j0 : J => p2 j0 .> g' j0) (t1 P2 (fun j0 : J => p2 j0 .> g' j0)))
      as [<- _]; [| cat].
    rewrite <- comp_assoc.
    destruct (H1 P1 (fun j0 : J => p1 j0 .> f' j0) (t2 P1 (fun j0 : J => p1 j0 .> f' j0)))
      as [<- _]; [| cat].
    rewrite comp_assoc, iso1, comp_id_r.
    reflexivity.
  - destruct (H1 P2 p2 (id P2)) as [_ <-]; [| cat].
    symmetry; apply H1; intros.
    rewrite comp_assoc.
    destruct (H1 P1 (fun j0 : J => p1 j0 .> f' j0) (t2 P1 (fun j0 : J => p1 j0 .> f' j0)))
      as [<- _]; [| cat].
    rewrite <- comp_assoc.
    destruct (H0 P2 (fun j0 : J => p2 j0 .> g' j0) (t1 P2 (fun j0 : J => p2 j0 .> g' j0)))
      as [<- _]; [| cat].
    rewrite comp_assoc, iso2, comp_id_r.
    reflexivity.
Defined.

Lemma small_and_indexed_products :
  forall
    {C : Cat} {A B : Ob C}
    (P : Ob C) (pA : Hom P A) (pB : Hom P B)
    (t : forall X : Ob C, Hom X A -> Hom X B -> Hom X P),
      product C P pA pB t
        <->
      exists
        (f := fun b : bool => if b then A else B)
        (p := fun b : bool => if b as b0 return (Hom P (if b0 then A else B))
                then pA else pB)
        (tuple := fun (X : Ob C) (f : forall j : bool, Hom X (if j then A else B)) =>
                    t X (f true) (f false)),
          f true = A /\ f false = B /\ indexed_product C P p tuple.
Proof.
  split.
  - unfold product, indexed_product, setoid_unique; cat.
    + destruct (H _ (f true) (f false)) as [[] uniq].
      destruct j; cbn; rewrite <- H0; assumption.
    + destruct (H _ (f true) (f false)) as [[] uniq].
      apply uniq. rewrite !H0. cat.
  - unfold product, indexed_product, setoid_unique.
    intros (_ & _ & H) X f g.
    pose
    (
      wut := fun j : bool =>
        if j return (Hom X (if j then A else B))
        then f
        else g
    ).
    destruct (H _ wut (t _ (wut true) (wut false))) as [H1 H2].
    specialize (H1 ltac:(reflexivity) true) as Ht; cbn in Ht.
    specialize (H1 ltac:(reflexivity) false) as Hf; cbn in Hf.
    cat.
    destruct (H _ wut y) as [H1' H2'].
    apply H2'. destruct j; cbn; assumption.
Qed.

Lemma nullary_prod :
  forall
    (C : Cat) (A : Empty_set -> Ob C)
    (T : Ob C) (delete : forall X : Ob C, Hom X T)
    (p : forall j : Empty_set, Hom T (A j))
    (tuple : forall (X : Ob C) (f : forall j : Empty_set, Hom X (A j)), Hom X T),
      terminal T delete -> indexed_product C T p tuple.
Proof.
  unfold terminal; red; cat.
  rewrite H, (H _ h).
  reflexivity.
Qed.

Lemma nullary_coprod :
  forall
    (C : Cat) (A : Empty_set -> Ob C) (I : Ob C)
    (create : forall X : Ob C, Hom I X)
    (p : forall j : Empty_set, Hom (A j) I)
    (cotuple : forall (X : Ob C) (f : forall j : Empty_set, Hom (A j) X), Hom I X),
     initial I create -> indexed_coproduct C I p cotuple.
Proof.
  unfold initial; red; cat.
  rewrite H, (H _ h).
  reflexivity.
Qed.

Lemma unary_prod_exists :
  forall (C : Cat) (A : unit -> Ob C),
    indexed_product C (A tt) (fun _ : unit => id (A tt)) (fun _ f => f tt).
Proof.
  red; cat.
Qed.

Lemma unary_coprod_exists :
  forall (C : Cat) (A : unit -> Ob C),
    indexed_coproduct C (A tt) (fun _ : unit => id (A tt)) (fun _ f => f tt).
Proof.
  red; cat.
Qed.