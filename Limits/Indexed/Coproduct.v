From Cat Require Import Cat.
From Cat.Limits Require Import Initial Terminal Coproduct.
From Cat.Limits.Indexed Require Import Product.

Section Traditional.

Definition isIndexedCoproduct
  (C : Cat) {J : Set} {A : J -> Ob C}
  (P : Ob C) (coproj : forall j : J, Hom (A j) P)
  (cotuple : forall (X : Ob C) (f : forall j : J, Hom (A j) X), Hom P X)
  : Prop :=
    forall (X : Ob C) (f : forall j : J, Hom (A j) X),
      setoid_unique (fun d : Hom P X => forall j : J, f j == coproj j .> d) (cotuple X f).

Lemma nullary_coprod :
  forall
    (C : Cat) (A : Empty_set -> Ob C) (I : Ob C)
    (create : forall X : Ob C, Hom I X)
    (p : forall j : Empty_set, Hom (A j) I)
    (cotuple : forall (X : Ob C) (f : forall j : Empty_set, Hom (A j) X), Hom I X),
     isInitial I create -> isIndexedCoproduct C I p cotuple.
Proof.
  unfold isInitial; red; cat.
  rewrite H, (H _ y).
  reflexivity.
Qed.

Lemma unary_coprod_exists :
  forall (C : Cat) (A : unit -> Ob C),
    isIndexedCoproduct C (A tt) (fun _ : unit => id (A tt)) (fun _ f => f tt).
Proof.
  red; cat.
Qed.

End Traditional.

Module Equational.

Definition indexed_coproduct'
  (C : Cat) {J : Set} {A : J -> Ob C}
  (P : Ob C) (coproj : forall j : J, Hom (A j) P)
  (cotuple : forall (X : Ob C) (f : forall j : J, Hom (A j) X), Hom P X)
  : Prop :=
    forall (X : Ob C) (f : forall j : J, Hom (A j) X) (h : Hom P X),
      cotuple _ f == h <-> forall j : J, f j == coproj j .> h.

Lemma nullary_coprod :
  forall
    (C : Cat) (A : Empty_set -> Ob C) (I : Ob C)
    (create : forall X : Ob C, Hom I X)
    (p : forall j : Empty_set, Hom (A j) I)
    (cotuple : forall (X : Ob C) (f : forall j : Empty_set, Hom (A j) X), Hom I X),
     isInitial I create -> indexed_coproduct' C I p cotuple.
Proof.
  unfold isInitial; red; cat.
  rewrite H, (H _ h).
  reflexivity.
Qed.

Lemma unary_coprod_exists :
  forall (C : Cat) (A : unit -> Ob C),
    indexed_coproduct' C (A tt) (fun _ : unit => id (A tt)) (fun _ f => f tt).
Proof.
  red; cat.
Qed.

End Equational.

Class HasIndexedCoproducts (C : Cat) : Type :=
{
  indexedCoproduct :
    forall J : Set, (J -> Ob C) -> Ob C;
  indexedCoproj :
    forall (J : Set) (A : J -> Ob C) (j : J),
      Hom (A j) (indexedCoproduct J A);
  cotuple :
    forall (J : Set) (A : J -> Ob C) (X : Ob C) (f : forall j : J, Hom (A j) X),
      Hom (indexedCoproduct J A) X;
  Proper_cotuple :
    forall
      (J : Set) (A : J -> Ob C) (X : Ob C)
      (f : forall j : J, Hom (A j) X) (g : forall j : J, Hom (A j) X),
        (forall j : J, f j == g j) -> cotuple J A X f == cotuple J A X g;
  is_indexed_coproduct :
    forall (J : Set) (A : J -> Ob C),
      isIndexedCoproduct C (indexedCoproduct J A) (indexedCoproj J A) (cotuple J A)
}.

Arguments indexedCoproduct [C _ J] _.
Arguments indexedCoproj   [C _ J A] _.
Arguments cotuple         [C _ J A X] _.

Section HasIndexedCoproducts.

Context
  [C : Cat]
  [hp : HasIndexedCoproducts C].

Lemma cotuple_indexedCoproj :
  forall (J : Set) (X : J -> Ob C) (Y : Ob C) (f : forall j : J, Hom (X j) Y) (j : J),
    indexedCoproj j .> cotuple f == f j.
Proof.
  intros. edestruct is_indexed_coproduct.
  rewrite <- H. reflexivity.
Qed.

Lemma cotuple_post :
  forall (J : Set) (X : J -> Ob C) (Y Z : Ob C) (f : forall j : J, Hom (X j) Y) (g : Hom Y Z),
    cotuple f .> g == cotuple (fun j : J => f j .> g).
Proof.
  intros. edestruct is_indexed_coproduct.
  rewrite <- H0.
    reflexivity.
    intros; cbn in *. assocl. rewrite cotuple_indexedCoproj. reflexivity.
Qed.

Lemma cotuple_id :
  forall (J : Set) (X : J -> Ob C),
    cotuple (@indexedCoproj C hp J X) == id (indexedCoproduct X).
Proof.
  intros. edestruct is_indexed_coproduct. apply H0. cat.
Qed.

Lemma cotuple_comp :
  forall
    (J : Set) (X X' : J -> Ob C) (Y : Ob C)
    (f : forall j : J, Hom (X j) (X' j))
    (g : forall j : J, Hom (X' j) Y),
      cotuple (fun j : J => f j .> g j)
        ==
      cotuple (fun j : J => f j .> indexedCoproj j) .> cotuple g.
Proof.
  intros. edestruct is_indexed_coproduct. apply H0. intros.
  rewrite <- comp_assoc, cotuple_indexedCoproj, -> comp_assoc, cotuple_indexedCoproj.
  reflexivity.
Qed.

End HasIndexedCoproducts.

#[export]
Instance HasIndexedProducts_Dual
  (C : Cat) (hp : HasIndexedCoproducts C) : HasIndexedProducts (Dual C) :=
{
  indexedProduct := @indexedCoproduct C hp;
  indexedProj := @indexedCoproj C hp;
  tuple := @cotuple C hp;
  Proper_tuple := @Proper_cotuple C hp;
  is_indexed_product := @is_indexed_coproduct C hp
}.

#[export]
Instance HasIndexedCoproducts_Dual
  (C : Cat) (hp : HasIndexedProducts C) : HasIndexedCoproducts (Dual C) :=
{
  indexedCoproduct := @indexedProduct C hp;
  indexedCoproj := @indexedProj C hp;
  cotuple := @tuple C hp;
  Proper_cotuple := @Proper_tuple C hp;
  is_indexed_coproduct := @is_indexed_product C hp
}.