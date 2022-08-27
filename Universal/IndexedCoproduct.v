From Cat Require Import Cat.

Class isIndexedCoproduct
  (C : Cat) {J : Set} {A : J -> Ob C}
  (P : Ob C) (coproj : forall j : J, Hom (A j) P)
  (cotuple : forall {X : Ob C} (f : forall j : J, Hom (A j) X), Hom P X)
  : Prop :=
{
  coproj_cotuple :
    forall {X : Ob C} (f : forall j : J, Hom (A j) X) (j : J),
      coproj j .> cotuple f == f j;
  cotuple_equiv :
    forall {X : Ob C} (h1 h2 : Hom P X),
      (forall j : J, coproj j .> h1 == coproj j .> h2) -> h1 == h2;
}.

#[export] Hint Mode isIndexedCoproduct ! ! ! ! ! ! : core.
#[export] Hint Mode isIndexedCoproduct ! ! ! - - - : core.

Lemma cotuple_equiv' :
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
  - now apply cotuple_equiv.
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
  apply cotuple_equiv; intros j.
  now rewrite !coproj_cotuple.
Defined.

Lemma cotuple_universal :
  forall h : Hom P X,
    cotuple f == h <-> forall j : J, f j == coproj j .> h.
Proof.
  now intros; rewrite cotuple_equiv'; setoid_rewrite coproj_cotuple.
Qed.

Lemma cotuple_unique :
  forall h : Hom P X,
    (forall j : J, coproj j .> h == f j) -> h == cotuple f.
Proof.
  now intros; apply cotuple_equiv; setoid_rewrite coproj_cotuple.
Qed.

Lemma cotuple_id :
  cotuple coproj == id P.
Proof.
  now rewrite cotuple_equiv'; intros j; rewrite coproj_cotuple, comp_id_r.
Qed.

Lemma cotuple_post :
  forall {Y : Ob C} (g : Hom X Y),
    cotuple f .> g == cotuple (fun j : J => f j .> g).
Proof.
  setoid_rewrite cotuple_equiv'; intros.
  now rewrite <- comp_assoc, !coproj_cotuple.
Qed.

End isIndexedCoproduct.

Class HasIndexedCoproducts'
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
  rewrite cotuple_post, cotuple_equiv'; intros j.
  now rewrite !coproj_cotuple, comp_assoc, coproj_cotuple.
Qed.

(*
#[export]
Instance HasIndexedProducts_Dual
  (C : Cat) (hp : HasIndexedCoproducts C) : HasIndexedProducts (Dual C) :=
{
  indexedProduct := @indexedCoproduct C hp;
  indexedProj := @coproj C hp;
  tuple := @cotuple C hp;
  Proper_tuple := @Proper_cotuple C hp;
  is_indexed_product := @is_indexed_coproduct C hp
}.

#[export]
Instance HasIndexedCoproducts_Dual
  (C : Cat) (hp : HasIndexedProducts C) : HasIndexedCoproducts (Dual C) :=
{
  indexedCoproduct := @indexedProduct C hp;
  coproj := @indexedProj C hp;
  cotuple := @tuple C hp;
  Proper_cotuple := @Proper_tuple C hp;
  is_indexed_coproduct := @is_indexed_product C hp
}.
*)