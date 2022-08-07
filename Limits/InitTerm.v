From Cat Require Export Cat.

Set Implicit Arguments.

Module Traditional.

Definition initial
  {C : Cat} (I : Ob C) (create : forall X : Ob C, Hom I X) : Prop :=
    forall (X : Ob C) (f : Hom I X), f == create X.

Definition terminal
  {C : Cat} (T : Ob C) (delete : forall X : Ob C, Hom X T) : Prop :=
    forall (X : Ob C) (f : Hom X T), f == delete X.

Definition isZero
  {C : Cat} (Z : Ob C)
  (create : forall X : Ob C, Hom Z X)
  (delete : forall X : Ob C, Hom X Z)
  : Prop := initial Z create /\ terminal Z delete.

Lemma initial_Dual :
  forall (C : Cat) (X : Ob C) (delete : forall X' : Ob C, Hom X' X),
    @initial (Dual C) X delete = @terminal C X delete.
Proof. reflexivity. Defined.

Lemma terminal_Dual :
  forall (C : Cat) (X : Ob C) (create : forall X' : Ob C, Hom X X'),
    @terminal (Dual C) X create = @initial C X create.
Proof. reflexivity. Defined.

Lemma isZero_Dual :
  forall
    (C : Cat) (X : Ob C)
    (create : forall X' : Ob C, Hom X X')
    (delete : forall X' : Ob C, Hom X' X),
      @isZero (Dual C) X delete create <-> @isZero C X create delete.
Proof. firstorder. Defined.

Lemma initial_uiso :
  forall
    (C : Cat) (A B : Ob C)
    (createA : forall X : Ob C, Hom A X)
    (createB : forall X : Ob C, Hom B X),
      initial A createA -> initial B createB -> A ~~ B.
Proof.
  unfold initial, uniquely_isomorphic, isomorphic.
  intros C A B createA createB createA_unique createB_unique.
  exists (createA B).
  split.
  - unfold isIso.
    exists (createB A).
    rewrite (createA_unique _ (id A)), (createB_unique _ (id B)), !createA_unique, !createB_unique.
    split; reflexivity.
  - intros. rewrite (createA_unique _ y). reflexivity.
Qed.

Lemma initial_iso :
  forall
    (C : Cat) (A B : Ob C)
    (createA : forall X : Ob C, Hom A X)
    (createB : forall X : Ob C, Hom B X),
      initial A createA -> initial B createB -> A ~ B.
Proof.
  intros. destruct (initial_uiso H H0). cat.
Qed.

Lemma initial_create_equiv :
  forall
    (C : Cat) (I : Ob C)
    (create : forall X : Ob C, Hom I X)
    (create' : forall X : Ob C, Hom I X),
      initial I create -> initial I create' ->
        forall X : Ob C, create X == create' X.
Proof.
  unfold initial.
  intros C I c1 c2 H1 H2 X.
  rewrite (H1 _ (c2 X)).
  reflexivity.
Qed.

Lemma iso_to_init_is_init :
  forall (C : Cat) (I : Ob C) (create : forall X : Ob C, Hom I X),
    initial I create ->
      forall {X : Ob C} (f : Hom X I), isIso f ->
        initial X (fun Y : Ob C => f .> create Y).
Proof.
  unfold initial.
  intros C I c H X f (f' & Heq1 & Heq2) Y g.
  rewrite <- (H _ (f' .> g)), <- comp_assoc, Heq1, comp_id_l.
  reflexivity.
Defined.

Lemma mor_to_init_is_ret :
  forall (C : Cat) (I : Ob C) (create : forall X : Ob C, Hom I X),
    initial I create ->
      forall {X : Ob C} (f : Hom X I), isRet f.
Proof.
  unfold initial, isRet.
  intros.
  exists (create X).
  rewrite (H _ (id I)), H.
  reflexivity.
Qed.

Lemma terminal_uiso :
  forall
    (C : Cat) (A B : Ob C)
    (deleteA : forall X : Ob C, Hom X A)
    (deleteB : forall X : Ob C, Hom X B),
      terminal A deleteA -> terminal B deleteB -> A ~~ B.
Proof.
  intro C.
  rewrite <- (Dual_Dual C); cbn; intros.
  rewrite terminal_Dual in *.
  rewrite Dual_uniquely_isomorphic.
  eapply initial_uiso; eassumption.
Qed.

Lemma terminal_iso :
  forall
    (C : Cat) (A B : Ob C)
    (deleteA : forall X : Ob C, Hom X A)
    (deleteB : forall X : Ob C, Hom X B),
      terminal A deleteA -> terminal B deleteB -> A ~ B.
Proof.
  intros. destruct (terminal_uiso H H0). cat.
Qed.

Lemma terminal_delete_equiv :
  forall
    (C : Cat) (T : Ob C)
    (delete : forall X : Ob C, Hom X T)
    (delete' : forall X : Ob C, Hom X T),
      terminal T delete -> terminal T delete' ->
        forall X : Ob C, delete X == delete' X.
Proof.
  unfold terminal.
  intros C T d1 d2 H1 H2 X.
  rewrite (H1 _ (d2 X)).
  reflexivity.
Qed.

Lemma iso_to_term_is_term :
  forall (C : Cat) (T : Ob C) (delete : forall X : Ob C, Hom X T),
    terminal T delete ->
      forall {X : Ob C} (f : Hom T X), isIso f ->
        terminal X (fun Y : Ob C => delete Y .> f).
Proof.
  unfold terminal.
  intros C T d H X f (f' & Heq1 & Heq2) Y g.
  rewrite <- (H _ (g .> f')), comp_assoc, Heq2, comp_id_r.
  reflexivity.
Defined.

Lemma mor_from_term_is_sec :
  forall (C : Cat) (T : Ob C) (delete : forall T' : Ob C, Hom T' T),
    terminal T delete ->
      forall {X : Ob C} (f : Hom T X), isSec f.
Proof.
  unfold terminal, isRet.
  intros.
  exists (delete X).
  rewrite (H _ (id T)), H.
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

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  delete : forall X : Ob C, Hom X term;
  delete_unique : forall [X : Ob C] (f : Hom X term), f == delete X;
}.

Arguments term   _ {_}.
Arguments delete {C _} _.

Ltac term := intros; repeat
match goal with
| |- context [?f] =>
  match type of f with
  | Hom _ (term _) => rewrite (delete_unique f)
  end
| |- ?x == ?x => reflexivity
end; try (cat; fail).

Class HasZero (C : Cat) : Type :=
{
  HasZero_HasInit :> HasInit C;
  HasZero_HasTerm :> HasTerm C;
  initial_is_terminal : init C = term C
}.

Coercion HasZero_HasInit : HasZero >-> HasInit.
Coercion HasZero_HasTerm : HasZero >-> HasTerm.

#[global] Hint Resolve create_unique delete_unique initial_is_terminal : core.

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

#[refine]
#[export]
Instance HasZero_Dual (C : Cat) (hz : HasZero C) : HasZero (Dual C) :=
{
  HasZero_HasInit := HasInit_Dual hz;
  HasZero_HasTerm := HasTerm_Dual hz;
}.
Proof. cat. Defined.

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
      initial X (fun Y : Ob C => f .> create Y).
Proof.
  unfold initial.
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
        terminal X (fun Y : Ob C => delete Y .> f).
Proof.
  unfold terminal.
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