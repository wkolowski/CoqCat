From Cat Require Export Cat.

Set Implicit Arguments.

Module Traditional.

Definition isInitial
  {C : Cat} (I : Ob C) (create : forall X : Ob C, Hom I X) : Prop :=
    forall (X : Ob C) (f : Hom I X), f == create X.

Lemma isInitial_uiso :
  forall
    (C : Cat) (A B : Ob C)
    (createA : forall X : Ob C, Hom A X)
    (createB : forall X : Ob C, Hom B X),
      isInitial A createA -> isInitial B createB -> A ~~ B.
Proof.
  unfold isInitial, uniquely_isomorphic, isomorphic.
  intros C A B createA createB createA_unique createB_unique.
  exists (createA B).
  split.
  - unfold isIso.
    exists (createB A).
    rewrite (createA_unique _ (id A)), (createB_unique _ (id B)),
            !createA_unique, !createB_unique.
    split; reflexivity.
  - intros. rewrite (createA_unique _ y). reflexivity.
Qed.

Lemma isInitial_iso :
  forall
    (C : Cat) (A B : Ob C)
    (createA : forall X : Ob C, Hom A X)
    (createB : forall X : Ob C, Hom B X),
      isInitial A createA -> isInitial B createB -> A ~ B.
Proof.
  intros. destruct (isInitial_uiso H H0). cat.
Qed.

Lemma isInitial_create_equiv :
  forall
    (C : Cat) (I : Ob C)
    (create : forall X : Ob C, Hom I X)
    (create' : forall X : Ob C, Hom I X),
      isInitial I create -> isInitial I create' ->
        forall X : Ob C, create X == create' X.
Proof.
  unfold isInitial.
  intros C I c1 c2 H1 H2 X.
  rewrite (H1 _ (c2 X)).
  reflexivity.
Qed.

Lemma iso_to_init_is_init :
  forall (C : Cat) (I : Ob C) (create : forall X : Ob C, Hom I X),
    isInitial I create ->
      forall {X : Ob C} (f : Hom X I), isIso f ->
        isInitial X (fun Y : Ob C => f .> create Y).
Proof.
  unfold isInitial.
  intros C I c H X f (f' & Heq1 & Heq2) Y g.
  rewrite <- (H _ (f' .> g)), <- comp_assoc, Heq1, comp_id_l.
  reflexivity.
Defined.

Lemma mor_to_init_is_ret :
  forall (C : Cat) (I : Ob C) (create : forall X : Ob C, Hom I X),
    isInitial I create ->
      forall {X : Ob C} (f : Hom X I), isRet f.
Proof.
  unfold isInitial, isRet.
  intros.
  exists (create X).
  rewrite (H _ (id I)), H.
  reflexivity.
Qed.

End Traditional.

Export Traditional.

Class HasInit (C : Cat) : Type :=
{
  init : Ob C;
  create : forall X : Ob C, Hom init X;
  create_unique : forall [X : Ob C] (f : Hom init X), f == create X;
}.

#[global] Hint Resolve create_unique : core.

Arguments init   _ {_}.
Arguments create {C _ } _.

Ltac init := intros; repeat
match goal with
| |- context [?f] =>
  match type of f with
  | Hom (init _) _ => rewrite (create_unique f)
  end
| |- ?x == ?x => reflexivity
end; try (cat; fail).

Lemma HasInit_uiso :
  forall (C : Cat) (hi1 hi2 : HasInit C),
    @init C hi1 ~~ @init C hi2.
Proof.
  unfold uniquely_isomorphic, isIso.
  intros.
  exists (create (init C)).
  split.
  - exists (create (init C)).
    split; rewrite !create_unique, (create_unique (id (init C))); reflexivity.
  - cbn. intros y _. rewrite (create_unique y). reflexivity.
Qed.

Lemma HasInit_iso :
  forall (C : Cat) (hi1 hi2 : HasInit C),
    @init C hi1 ~ @init C hi2.
Proof.
  intros. destruct (HasInit_uiso hi1 hi2). cat.
Qed.

Lemma HasInit_create_equiv :
  forall (C : Cat) (hi1 hi2 : HasInit C),
    @init C hi1 = @init C hi2 ->
      forall X : Ob C, JMequiv (@create _ hi1 X) (@create _ hi2 X).
Proof.
  intros C [I1 c1 H1] [I2 c2 H2] Heq X; cbn in *.
  destruct Heq.
  constructor.
  rewrite (H1 _ (c2 _)).
  reflexivity.
Qed.

Lemma iso_to_init_is_init :
  forall (C : Cat) (hi : HasInit C),
    forall {X : Ob C} (f : Hom X (init C)), isIso f ->
      isInitial X (fun Y : Ob C => f .> create Y).
Proof.
  unfold isInitial.
  intros C [I c H] X f (f' & Heq1 & Heq2) Y g.
  rewrite <- (H _ (f' .> g)), <- comp_assoc, Heq1, comp_id_l.
  reflexivity.
Defined.

Lemma mor_to_init_is_ret :
  forall (C : Cat) (hi : HasInit C) (X : Ob C) (f : Hom X (init C)),
    isRet f.
Proof.
  intros; red.
  exists (create X).
  rewrite create_unique, <- (create_unique (id _)).
  reflexivity.
Qed.