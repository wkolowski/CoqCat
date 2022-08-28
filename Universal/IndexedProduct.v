From Cat Require Import Cat.
From Cat.Universal Require Import Product Terminal.

Set Implicit Arguments.

Class isIndexedProduct
  (C : Cat) {J : Set} {A : J -> Ob C}
  (P : Ob C) (proj : forall j : J, Hom P (A j))
  (tuple : forall {X : Ob C} (f : forall j : J, Hom X (A j)), Hom X P)
  : Prop :=
{
  tuple_out :
    forall {X : Ob C} (f : forall j : J, Hom X (A j)) (j : J),
      tuple f .> proj j == f j;
  tuple_equiv :
    forall {X : Ob C} (f g : Hom X P),
      (forall j : J, f .> proj j == g .> proj j) -> f == g;
}.

#[export] Hint Mode isIndexedProduct ! ! ! ! ! ! : core.
#[export] Hint Mode isIndexedProduct ! ! ! - - - : core.

Lemma tuple_equiv' :
  forall
    {C : Cat} {J : Set} {A : J -> Ob C}
    {P : Ob C} {proj : forall j : J, Hom P (A j)}
    {tuple : forall {X : Ob C} (f : forall j : J, Hom X (A j)), Hom X P}
    {isP : isIndexedProduct C P proj (@tuple)}
    {X : Ob C} (f g : Hom X P),
      f == g <-> forall j : J, f .> proj j == g .> proj j.
Proof.
  split.
  - now intros Heq j; rewrite Heq.
  - now apply tuple_equiv.
Qed.

Section isIndexedProduct.

Context
  {C : Cat} {J : Set} {A : J -> Ob C}
  {P : Ob C} {proj : forall j : J, Hom P (A j)}
  {tuple : forall {X : Ob C} (f : forall j : J, Hom X (A j)), Hom X P}
  {isP : isIndexedProduct C P proj (@tuple)}
  {X Y : Ob C} (f : forall j : J, Hom X (A j)).

Arguments tuple {X} _.

#[global] Instance Proper_tuple :
  Proper (equiv ==> equiv) (@tuple X).
Proof.
  intros h1 h2 Heq.
  apply tuple_equiv; intros j.
  now rewrite !tuple_out.
Defined.

Lemma tuple_universal :
  forall h : Hom X P,
    tuple f == h <-> forall j : J, f j == h .> proj j.
Proof.
  now intros; rewrite tuple_equiv'; setoid_rewrite tuple_out.
Qed.

Lemma tuple_unique :
  forall h : Hom X P,
    (forall j : J, h .> proj j == f j) -> h == tuple f.
Proof.
  now intros; apply tuple_equiv; setoid_rewrite tuple_out.
Qed.

Lemma tuple_id :
  tuple proj == id P.
Proof.
  now rewrite tuple_equiv'; setoid_rewrite tuple_out.
Qed.

Lemma tuple_pre :
  forall h : Hom Y X,
    tuple (fun j => h .> f j) == h .> tuple f.
Proof.
  setoid_rewrite tuple_equiv'; intros h j.
  now rewrite comp_assoc, !tuple_out.
Qed.

End isIndexedProduct.

Lemma isIndexedProduct_iso_unique :
  forall
    (C : Cat) (J : Set) (A : J -> Ob C)
    (P1 : Ob C) (proj1 : forall j : J, Hom P1 (A j))
    (tuple1 : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P1)
    (P2 : Ob C) (proj2 : forall j : J, Hom P2 (A j))
    (tuple2 : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P2),
      isIndexedProduct C P1 proj1 tuple1 ->
      isIndexedProduct C P2 proj2 tuple2 ->
        P1 ~ P2.
Proof.
  intros * H1 H2.
  exists (tuple2 _ proj1), (tuple1 _ proj2).
  rewrite <- !tuple_pre, !tuple_equiv'; split; intros.
  - now rewrite !tuple_out, comp_id_l.
  - now rewrite !tuple_out, comp_id_l.
Qed.

Lemma isIndexedProduct_iso_unique2 :
  forall
    (C : Cat) (J : Set) (A B : J -> Ob C)
    (P1 : Ob C) (p1 : forall j : J, Hom P1 (A j))
    (t1 : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P1)
    (P2 : Ob C) (p2 : forall j : J, Hom P2 (B j))
    (t2 : forall (X : Ob C) (f : forall j : J, Hom X (B j)), Hom X P2),
      (forall j : J, A j ~ B j) ->
      isIndexedProduct C P1 p1 t1 ->
      isIndexedProduct C P2 p2 t2 ->
        P1 ~ P2.
Proof.
  unfold isomorphic, isIso.
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
  - rewrite tuple_equiv'; intros j.
    now rewrite comp_assoc, tuple_out, <- comp_assoc, tuple_out, comp_assoc,
      iso1, comp_id_l, comp_id_r.
  - rewrite tuple_equiv'; intros j.
    now rewrite comp_assoc, tuple_out, <- comp_assoc, tuple_out, comp_assoc,
      iso2, comp_id_l, comp_id_r.
Defined.

Lemma small_and_isIndexedProducts :
  forall
    {C : Cat} {A B : Ob C}
    (P : Ob C) (pA : Hom P A) (pB : Hom P B)
    (t : forall X : Ob C, Hom X A -> Hom X B -> Hom X P),
      isProduct C P pA pB t
        <->
      exists
        (f := fun b : bool => if b then A else B)
        (p := fun b : bool => if b as b0 return (Hom P (if b0 then A else B))
                then pA else pB)
        (tuple := fun (X : Ob C) (f : forall j : bool, Hom X (if j then A else B)) =>
                    t X (f true) (f false)),
          isIndexedProduct C P p tuple.
Proof.
  split; cbn; intros * HP.
  - split.
    + intros X f [].
      * now rewrite fpair_outl.
      * now rewrite fpair_outr.
    + now intros X f g H; rewrite fpair_equiv', (H false), (H true).
  - split.
    + intros X f g.
    pose
    (
      wut := fun j : bool =>
        if j return (Hom X (if j then A else B))
        then f
        else g
    ).
    destruct HP. apply (tuple_out0 _ wut true).
    + intros X f g.
    pose
    (
      wut := fun j : bool =>
        if j return (Hom X (if j then A else B))
        then f
        else g
    ).
    destruct HP. apply (tuple_out0 _ wut false).
  + intros * H1 H2. destruct HP.
    apply tuple_equiv0. now intros []; cbn.
Qed.

Lemma nullary_prod :
  forall
    (C : Cat) (A : Empty_set -> Ob C)
    (T : Ob C) (delete : forall X : Ob C, Hom X T)
    (p : forall j : Empty_set, Hom T (A j))
    (tuple : forall (X : Ob C) (f : forall j : Empty_set, Hom X (A j)), Hom X T),
      isTerminal C T delete -> isIndexedProduct C T p tuple.
Proof.
  unfold isTerminal; split; intros.
  - easy.
  - apply H.
Qed.

Lemma unary_prod_exists :
  forall (C : Cat) (A : unit -> Ob C),
    isIndexedProduct C (A tt) (fun _ : unit => id (A tt)) (fun _ f => f tt).
Proof.
  split; cat.
Qed.

(* Dependent type bullshit. This is harder than I thought. *)
Lemma isIndexedProduct_comm :
  forall
    (C : Cat) (J : Set) (A : J -> Ob C)
    (P : Ob C) (p : forall j : J, Hom P (A j))
    (tuple : forall (X : Ob C) (f : forall j : J, Hom X (A j)), Hom X P)
    (f : J -> J) 
    (p' : forall j : J, Hom P (A (f j)))
    (tuple' : forall (X : Ob C) (f : forall j : J, Hom X (A (f j))), Hom X P),
      (forall j : J, p' j = p (f j)) ->
        bijective f -> isIndexedProduct C P p tuple -> isIndexedProduct C P p' tuple'.
Proof.
  unfold bijective, injective, surjective.
  destruct 2 as [inj sur]; intros.
  assert (g : {g : J -> J |
    (forall j : J, f (g j) = j) /\ (forall j : J, g (f j) = j)}).
    exists (fun j : J => proj1_sig (constructive_indefinite_description _ (sur j))).
    split; intros.
      destruct (constructive_indefinite_description _ (sur j)). auto.
      destruct (constructive_indefinite_description _ (sur (f j))). auto.
  destruct g as [g [g_inv1 g_inv2]].
  assert (h : {h : forall j : J, Hom P (A (f (g j))) |
  (forall j : J, h j = p (f (g j)))}).
Abort.

Class HasIndexedProducts'
  (C : Cat) (indexedProduct : forall {J : Set} (A : J -> Ob C), Ob C) : Type :=
{
  proj :
    forall {J : Set} {A : J -> Ob C} (j : J), Hom (indexedProduct A) (A j);
  tuple :
    forall {J : Set} {A : J -> Ob C} {X : Ob C} (f : forall j : J, Hom X (A j)),
      Hom X (indexedProduct A);
  HasIndexedProducts_isIndexedProduct :>
    forall {J : Set} {A : J -> Ob C},
      isIndexedProduct C (indexedProduct A) (@proj J A) (@tuple J A)
}.

Arguments proj  {C _ _ J A} _.
Arguments tuple {C _ _ J A X} _.

Class HasIndexedProducts (C : Cat) : Type :=
{
  indexedProduct : forall {J : Set} (A : J -> Ob C), Ob C;
  HasIndexedProducts'_HasIndexedProducts :> HasIndexedProducts' C (@indexedProduct);
}.

Arguments indexedProduct {C _ J} _.

Coercion HasIndexedProducts'_HasIndexedProducts :
  HasIndexedProducts >-> HasIndexedProducts'.

Lemma tuple_comp :
  forall
    {C : Cat} {hip : HasIndexedProducts C}
    {X : Ob C} {J : Set} {A B : J -> Ob C}
    (f : forall j : J, Hom X (A j)) (g : forall j : J, Hom (A j) (B j)),
      tuple (fun j : J => f j .> g j)
        ==
      tuple f .> tuple (fun j : J => proj j .> g j).
Proof.
  intros.
  rewrite <- tuple_pre, tuple_equiv'; intros j.
  now rewrite !tuple_out, <- comp_assoc, tuple_out.
Qed.