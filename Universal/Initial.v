From Cat Require Export Cat.

Set Implicit Arguments.

Class isInitial (C : Cat) (I : Ob C) (create : forall X : Ob C, Hom I X) : Prop :=
  equiv_initial : forall {X : Ob C} (f g : Hom I X), f == g.

Arguments equiv_initial {C I create isInitial X f} _.

#[export] Hint Mode isInitial ! ! ! : core.
#[export] Hint Mode isInitial ! - - : core.

Lemma equiv_initial' :
  forall
    {C : Cat} {I : Ob C} {create : forall X : Ob C, Hom I X}
    {isI : isInitial C I create}
    {X : Ob C} (h1 h2 : Hom I X),
      h1 == h2 <-> True.
Proof.
  now firstorder.
Qed.

Ltac initial_simpl := rewrite ?equiv_initial'.

Class HasInit (C : Cat) : Type :=
{
  init : Ob C;
  create : forall X : Ob C, Hom init X;
  isInitial_HasInit' :: isInitial C init create;
}.

Arguments init   _ {_}.
Arguments create {C _} _.

Lemma isInitial_uiso :
  forall
    (C : Cat)
    (I1 : Ob C) (create1 : forall X : Ob C, Hom I1 X)
    (I2 : Ob C) (create2 : forall X : Ob C, Hom I2 X),
      isInitial C I1 create1 ->
      isInitial C I2 create2 ->
        I1 ~~ I2.
Proof.
  intros C I1 create1 I2 create2 H1 H2.
  exists (create1 I2).
  split.
  - exists (create2 I1).
    now split; apply equiv_initial.
  - now intros; apply equiv_initial.
Qed.

Lemma isInitial_iso :
  forall
    (C : Cat)
    (I1 : Ob C) (create1 : forall X : Ob C, Hom I1 X)
    (I2 : Ob C) (create2 : forall X : Ob C, Hom I2 X),
      isInitial C I1 create1 ->
      isInitial C I2 create2 ->
        I1 ~ I2.
Proof.
  now intros * H1 H2; destruct (isInitial_uiso H1 H2) as [i []]; exists i.
Qed.

Lemma isInitial_equiv_create :
  forall
    (C : Cat)
    (I : Ob C) (create1 create2 : forall X : Ob C, Hom I X),
      isInitial C I create1 ->
      isInitial C I create2 ->
        forall X : Ob C, create1 X == create2 X.
Proof.
  now intros; apply equiv_initial.
Qed.

Lemma iso_to_init_is_init :
  forall (C : Cat) (I : Ob C) (create : forall X : Ob C, Hom I X),
    isInitial C I create ->
      forall {X : Ob C} (f : Hom X I), isIso f ->
        isInitial C X (fun Y : Ob C => f .> create Y).
Proof.
  intros C I c H X f (f' & Heq1 & Heq2) Y g1 g2.
  now rewrite <- comp_id_l, <- Heq1, comp_assoc, (equiv_initial (f' .> g2)),
    <- comp_assoc, Heq1, comp_id_l.
Defined.

Lemma mor_to_init_is_ret :
  forall (C : Cat) (I : Ob C) (create : forall X : Ob C, Hom I X),
    isInitial C I create ->
      forall {X : Ob C} (f : Hom X I), isRet f.
Proof.
  unfold isRet; intros.
  exists (create0 X).
  now apply equiv_initial.
Qed.

Class HasStrictInit (C : Cat) {hi : HasInit C} : Type :=
  isStrictlyInitial : forall {X : Ob C} (f : Hom X (init C)), isIso' f.

#[export] Hint Mode HasStrictInit ! ! : core.
#[export] Hint Mode HasStrictInit ! - : core.

Arguments HasStrictInit _ {hi}.
Arguments isStrictlyInitial {C hi _} _.
