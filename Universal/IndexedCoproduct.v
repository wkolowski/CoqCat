From Cat Require Import Cat.
From Cat.Universal Require Import Initial.

Class isIndexedCoproduct
  (C : Cat) {J : Set} {A : J -> Ob C}
  (P : Ob C) (coproj : forall j : J, Hom (A j) P)
  (cotuple : forall {X : Ob C} (f : forall j : J, Hom (A j) X), Hom P X)
  : Prop :=
{
  coproj_cotuple :
    forall {X : Ob C} (f : forall j : J, Hom (A j) X) (j : J),
      coproj j .> cotuple f == f j;
  equiv_indexedCoproduct :
    forall {X : Ob C} (h1 h2 : Hom P X),
      (forall j : J, coproj j .> h1 == coproj j .> h2) -> h1 == h2;
}.

#[export] Hint Mode isIndexedCoproduct ! ! ! ! ! ! : core.
#[export] Hint Mode isIndexedCoproduct ! ! ! - - - : core.

Lemma equiv_indexedCoproduct' :
  forall
    {C : Cat} {J : Set} {A : J -> Ob C}
    {P : Ob C} {coproj : forall j : J, Hom (A j) P}
    {cotuple : forall {X : Ob C} (f : forall j : J, Hom (A j) X), Hom P X}
    {isIC : isIndexedCoproduct C P coproj (@cotuple)}
    {X : Ob C} (h1 h2 : Hom P X),
      h1 == h2 <-> (forall j : J, coproj j .> h1 == coproj j .> h2).
Proof.
  split.
  - now intros Heq j; rewrite Heq.
  - now apply equiv_indexedCoproduct.
Qed.

Section isIndexedCoproduct.

Context
  {C : Cat} {J : Set} {A : J -> Ob C}
  {P : Ob C} {coproj : forall j : J, Hom (A j) P}
  {cotuple : forall {X : Ob C} (f : forall j : J, Hom (A j) X), Hom P X}
  {isIC : isIndexedCoproduct C P coproj (@cotuple)}
  {X : Ob C} {f : forall j : J, Hom (A j) X}.

Arguments cotuple {X} _.

#[global] Instance Proper_cotuple :
  Proper (equiv ==> equiv) (@cotuple X).
Proof.
  intros h1 h2 Heq.
  apply equiv_indexedCoproduct; intros j.
  now rewrite !coproj_cotuple.
Defined.

Lemma cotuple_universal :
  forall h : Hom P X,
    cotuple f == h <-> forall j : J, f j == coproj j .> h.
Proof.
  now intros; rewrite equiv_indexedCoproduct'; setoid_rewrite coproj_cotuple.
Qed.

Lemma cotuple_unique :
  forall h : Hom P X,
    (forall j : J, coproj j .> h == f j) -> h == cotuple f.
Proof.
  now intros; apply equiv_indexedCoproduct; setoid_rewrite coproj_cotuple.
Qed.

Lemma cotuple_id :
  cotuple coproj == id P.
Proof.
  now rewrite equiv_indexedCoproduct'; intros j; rewrite coproj_cotuple, comp_id_r.
Qed.

Lemma cotuple_post :
  forall {Y : Ob C} (g : Hom X Y),
    cotuple f .> g == cotuple (fun j : J => f j .> g).
Proof.
  setoid_rewrite equiv_indexedCoproduct'; intros.
  now rewrite <- comp_assoc, !coproj_cotuple.
Qed.

End isIndexedCoproduct.

Lemma nullary_coproduct :
  forall
    (C : Cat) (A : Empty_set -> Ob C) (I : Ob C)
    (create : forall X : Ob C, Hom I X)
    (p : forall j : Empty_set, Hom (A j) I)
    (cotuple : forall (X : Ob C) (f : forall j : Empty_set, Hom (A j) X), Hom I X),
      isInitial C I create -> isIndexedCoproduct C I p cotuple.
Proof.
  now split; intros; [| apply equiv_initial].
Qed.

Lemma unary_coprod_exists :
  forall (C : Cat) (A : unit -> Ob C),
    isIndexedCoproduct C (A tt) (fun _ : unit => id (A tt)) (fun _ f => f tt).
Proof.
  split; cat.
Qed.

(* Class HasIndexedCoproducts'
  (C : Cat) (indexedCoproduct : forall J : Set, (J -> Ob C) -> Ob C) : Type :=
{
  coproj :
    forall (J : Set) (A : J -> Ob C) (j : J),
      Hom (A j) (indexedCoproduct J A);
  cotuple :
    forall (J : Set) (A : J -> Ob C) (X : Ob C) (f : forall j : J, Hom (A j) X),
      Hom (indexedCoproduct J A) X;
  isIndexedCoproduct_HasIndexedCoproducts' :>
    forall (J : Set) (A : J -> Ob C),
      isIndexedCoproduct C (indexedCoproduct J A) (coproj J A) (cotuple J A)
}.

Arguments coproj  {C _ _ J A} _.
Arguments cotuple {C _ _ J A X} _.

Class HasIndexedCoproducts (C : Cat) : Type :=
{
  indexedCoproduct : forall J : Set, (J -> Ob C) -> Ob C;
  HasIndexedCoproducts'_HasIndexedCoproducts :> HasIndexedCoproducts' C (@indexedCoproduct);
}.

Arguments indexedCoproduct [C _ J] _.

Coercion HasIndexedCoproducts'_HasIndexedCoproducts :
  HasIndexedCoproducts >-> HasIndexedCoproducts'. *)

Class HasIndexedCoproducts (C : Cat) : Type :=
{
  indexedCoproduct : forall J : Set, (J -> Ob C) -> Ob C;
  coproj :
    forall (J : Set) (A : J -> Ob C) (j : J),
      Hom (A j) (indexedCoproduct J A);
  cotuple :
    forall (J : Set) (A : J -> Ob C) (X : Ob C) (f : forall j : J, Hom (A j) X),
      Hom (indexedCoproduct J A) X;
  isIndexedCoproduct_HasIndexedCoproducts' :>
    forall (J : Set) (A : J -> Ob C),
      isIndexedCoproduct C (indexedCoproduct J A) (coproj J A) (cotuple J A)
}.

Arguments indexedCoproduct {C _ J} _.
Arguments coproj           {C _ J A} _.
Arguments cotuple          {C _ J A X} _.

Lemma cotuple_comp :
  forall
    {C : Cat} {hip : HasIndexedCoproducts C}
    {X : Ob C} {J : Set} {A B : J -> Ob C}
    (f : forall j : J, Hom (A j) (B j)) (g : forall j : J, Hom (B j) X),
      cotuple (fun j : J => f j .> g j)
        ==
      cotuple (fun j : J => f j .> coproj j) .> cotuple g.
Proof.
  intros.
  rewrite cotuple_post, equiv_indexedCoproduct'; intros j.
  now rewrite !coproj_cotuple, comp_assoc, coproj_cotuple.
Qed.