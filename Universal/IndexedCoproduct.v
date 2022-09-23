From Cat Require Import Cat.
From Cat.Universal Require Import Initial.

Class isIndexedCoproduct
  (C : Cat) {J : Set} {A : J -> Ob C}
  (P : Ob C) (inj : forall j : J, Hom (A j) P)
  (cotuple : forall {X : Ob C} (f : forall j : J, Hom (A j) X), Hom P X)
  : Prop :=
{
  inj_cotuple :
    forall {X : Ob C} (f : forall j : J, Hom (A j) X) (j : J),
      inj j .> cotuple f == f j;
  equiv_indexedCoproduct :
    forall {X : Ob C} (h1 h2 : Hom P X),
      (forall j : J, inj j .> h1 == inj j .> h2) -> h1 == h2;
}.

#[export] Hint Mode isIndexedCoproduct ! ! ! ! ! ! : core.
#[export] Hint Mode isIndexedCoproduct ! ! ! - - - : core.

Lemma equiv_indexedCoproduct' :
  forall
    {C : Cat} {J : Set} {A : J -> Ob C}
    {P : Ob C} {inj : forall j : J, Hom (A j) P}
    {cotuple : forall {X : Ob C} (f : forall j : J, Hom (A j) X), Hom P X}
    {isIC : isIndexedCoproduct C P inj (@cotuple)}
    {X : Ob C} (h1 h2 : Hom P X),
      h1 == h2 <-> (forall j : J, inj j .> h1 == inj j .> h2).
Proof.
  split.
  - now intros Heq j; rewrite Heq.
  - now apply equiv_indexedCoproduct.
Qed.

Section isIndexedCoproduct.

Context
  {C : Cat} {J : Set} {A : J -> Ob C}
  {P : Ob C} {inj : forall j : J, Hom (A j) P}
  {cotuple : forall {X : Ob C} (f : forall j : J, Hom (A j) X), Hom P X}
  {isIC : isIndexedCoproduct C P inj (@cotuple)}
  {X : Ob C} {f : forall j : J, Hom (A j) X}.

Arguments cotuple {X} _.

#[global] Instance Proper_cotuple :
  Proper (equiv ==> equiv) (@cotuple X).
Proof.
  intros h1 h2 Heq.
  apply equiv_indexedCoproduct; intros j.
  now rewrite !inj_cotuple.
Defined.

Lemma cotuple_universal :
  forall h : Hom P X,
    cotuple f == h <-> forall j : J, f j == inj j .> h.
Proof.
  now intros; rewrite equiv_indexedCoproduct'; setoid_rewrite inj_cotuple.
Qed.

Lemma cotuple_unique :
  forall h : Hom P X,
    (forall j : J, inj j .> h == f j) -> h == cotuple f.
Proof.
  now intros; apply equiv_indexedCoproduct; setoid_rewrite inj_cotuple.
Qed.

Lemma cotuple_id :
  cotuple inj == id P.
Proof.
  now rewrite equiv_indexedCoproduct'; intros j; rewrite inj_cotuple, comp_id_r.
Qed.

Lemma cotuple_comp :
  forall {Y : Ob C} (g : Hom X Y),
    cotuple f .> g == cotuple (fun j : J => f j .> g).
Proof.
  setoid_rewrite equiv_indexedCoproduct'; intros.
  now rewrite <- comp_assoc, !inj_cotuple.
Qed.

End isIndexedCoproduct.

Ltac indexedCoproduct_simpl := repeat (
  try setoid_rewrite equiv_indexedCoproduct';
  try setoid_rewrite inj_cotuple;
  try setoid_rewrite cotuple_id;
  try setoid_rewrite cotuple_comp;
  try setoid_rewrite comp_id_l;
  try setoid_rewrite comp_id_r;
  try setoid_rewrite comp_assoc).

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
  now split; cat.
Qed.

Class HasIndexedCoproducts (C : Cat) : Type :=
{
  indexedCoproduct : forall J : Set, (J -> Ob C) -> Ob C;
  inj :
    forall (J : Set) (A : J -> Ob C) (j : J),
      Hom (A j) (indexedCoproduct J A);
  cotuple :
    forall (J : Set) (A : J -> Ob C) (X : Ob C) (f : forall j : J, Hom (A j) X),
      Hom (indexedCoproduct J A) X;
  isIndexedCoproduct_HasIndexedCoproducts' :>
    forall (J : Set) (A : J -> Ob C),
      isIndexedCoproduct C (indexedCoproduct J A) (inj J A) (cotuple J A)
}.

Arguments indexedCoproduct {C _ J} _.
Arguments inj           {C _ J A} _.
Arguments cotuple          {C _ J A X} _.

Lemma cotuple_comp' :
  forall
    {C : Cat} {hip : HasIndexedCoproducts C}
    {X : Ob C} {J : Set} {A B : J -> Ob C}
    (f : forall j : J, Hom (A j) (B j)) (g : forall j : J, Hom (B j) X),
      cotuple (fun j : J => f j .> g j)
        ==
      cotuple (fun j : J => f j .> inj j) .> cotuple g.
Proof.
  intros.
  rewrite cotuple_comp, equiv_indexedCoproduct'; intros j.
  now rewrite !inj_cotuple, comp_assoc, inj_cotuple.
Qed.