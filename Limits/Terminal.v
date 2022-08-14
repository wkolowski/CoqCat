From Cat Require Export Cat.
From Cat.Limits Require Import Initial.

Set Implicit Arguments.

Module Traditional.

Definition isTerminal
  {C : Cat} (T : Ob C) (delete : forall X : Ob C, Hom X T) : Prop :=
    forall (X : Ob C) (f : Hom X T), f == delete X.

Lemma isInitial_Dual :
  forall (C : Cat) (X : Ob C) (delete : forall X' : Ob C, Hom X' X),
    @isInitial (Dual C) X delete = @isTerminal C X delete.
Proof. reflexivity. Defined.

Lemma isTerminal_Dual :
  forall (C : Cat) (X : Ob C) (create : forall X' : Ob C, Hom X X'),
    @isTerminal (Dual C) X create = @isInitial C X create.
Proof. reflexivity. Defined.

Lemma isTerminal_uiso :
  forall
    (C : Cat)
    (T1 : Ob C) (delete1 : forall X : Ob C, Hom X T1)
    (T2 : Ob C) (delete2 : forall X : Ob C, Hom X T2),
      isTerminal T1 delete1 ->
      isTerminal T2 delete2 ->
        T1 ~~ T2.
Proof.
  intro C.
  rewrite <- (Dual_Dual C); cbn; intros.
  rewrite isTerminal_Dual in *.
  rewrite Dual_uniquely_isomorphic.
  eapply isInitial_uiso; eassumption.
Qed.

Lemma isTerminal_iso :
  forall
    (C : Cat)
    (T1 : Ob C) (delete1 : forall X : Ob C, Hom X T1)
    (T2 : Ob C) (delete2 : forall X : Ob C, Hom X T2),
      isTerminal T1 delete1 ->
      isTerminal T2 delete2 ->
        T1 ~ T2.
Proof.
  intros. destruct (isTerminal_uiso H H0). cat.
Qed.

Lemma isTerminal_delete_equiv :
  forall
    (C : Cat)
    (T : Ob C) (delete1 delete2 : forall X : Ob C, Hom X T),
      isTerminal T delete1 ->
      isTerminal T delete2 ->
        forall X : Ob C, delete1 X == delete2 X.
Proof.
  unfold isTerminal.
  intros C T d1 d2 H1 H2 X.
  rewrite (H1 _ (d2 X)).
  reflexivity.
Qed.

Lemma iso_to_term_is_term :
  forall (C : Cat) (T : Ob C) (delete : forall X : Ob C, Hom X T),
    isTerminal T delete ->
      forall {X : Ob C} (f : Hom T X), isIso f ->
        isTerminal X (fun Y : Ob C => delete Y .> f).
Proof.
  unfold isTerminal.
  intros C T d H X f (f' & Heq1 & Heq2) Y g.
  rewrite <- (H _ (g .> f')), comp_assoc, Heq2, comp_id_r.
  reflexivity.
Defined.

Lemma mor_from_term_is_sec :
  forall (C : Cat) (T : Ob C) (delete : forall T' : Ob C, Hom T' T),
    isTerminal T delete ->
      forall {X : Ob C} (f : Hom T X), isSec f.
Proof.
  unfold isTerminal, isRet.
  intros.
  exists (delete X).
  rewrite (H _ (id T)), H.
  reflexivity.
Qed.

End Traditional.

Export Traditional.

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  delete : forall X : Ob C, Hom X term;
  delete_unique : forall [X : Ob C] (f : Hom X term), f == delete X;
}.

Arguments term   _ {_}.
Arguments delete {C _} _.

#[global] Hint Resolve delete_unique : core.

Ltac term := intros; repeat
match goal with
| |- context [?f] =>
  match type of f with
  | Hom _ (term _) => rewrite (delete_unique f)
  end
| |- ?x == ?x => reflexivity
end; try (cat; fail).

Lemma HasTerm_uiso :
  forall (C : Cat) (ht1 ht2 : HasTerm C),
    @term C ht1 ~~ @term C ht2.
Proof.
  unfold uniquely_isomorphic, isIso.
  intros.
  exists (delete (term C)).
  split.
  - exists (delete (term C)).
    split; rewrite !delete_unique, (delete_unique (id (term C))); reflexivity.
  - cbn. intros y _. rewrite (delete_unique y). reflexivity.
Qed.

Lemma HasTerm_iso :
  forall (C : Cat) (ht1 ht2 : HasTerm C),
    @term C ht1 ~ @term C ht2.
Proof.
  intros. destruct (HasTerm_uiso ht1 ht2). cat.
Qed.

Lemma HasTerm_delete_equiv :
  forall (C : Cat) (ht1 ht2 : HasTerm C),
    @term C ht1 = @term C ht2 ->
      forall X : Ob C, JMequiv (@delete _ ht1 X) (@delete _ ht2 X).
Proof.
  intros C [T1 d1 H1] [T2 d2 H2] Heq X; cbn in *.
  destruct Heq.
  constructor.
  rewrite (H1 _ (d2 _)).
  reflexivity.
Qed.

Lemma iso_to_term_is_term :
  forall (C : Cat) (ht : HasTerm C),
      forall {X : Ob C} (f : Hom (term C) X), isIso f ->
        isTerminal X (fun Y : Ob C => delete Y .> f).
Proof.
  unfold isTerminal.
  intros C [T d H] X f (f' & Heq1 & Heq2) Y g.
  rewrite <- (H _ (g .> f')), comp_assoc, Heq2, comp_id_r.
  reflexivity.
Defined.

Lemma mor_from_term_is_sec :
  forall (C : Cat) (ht : HasTerm C) (X : Ob C) (f : Hom (term C) X),
    isSec f.
Proof.
  intros; red.
  exists (delete X).
  rewrite delete_unique, <- (delete_unique (id _)).
  reflexivity.
Qed.

#[refine]
#[export]
Instance HasTerm_Dual (C : Cat) (hi : HasInit C) : HasTerm (Dual C) :=
{
  term := init C;
  delete := @create C hi
}.
Proof. cat. Defined.

#[refine]
#[export]
Instance HasInit_Dual (C : Cat) (ht : HasTerm C) : HasInit (Dual C) :=
{
  init := term C;
  create := @delete C ht
}.
Proof. cat. Defined.