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
  firstorder.
Qed.

Ltac initial_simpl := rewrite ?equiv_initial'.

Class HasInit (C : Cat) : Type :=
{
  init : Ob C;
  create : forall X : Ob C, Hom init X;
  isInitial_HasInit' :> isInitial C init create;
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
    split; apply equiv_initial.
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
  intros. destruct (isInitial_uiso H H0). cat.
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
  apply equiv_initial.
Qed.

Module wut. (* TODO: are separate lemmas for Has* needed? *)

Lemma HasInit_uiso :
  forall (C : Cat) (hi1 hi2 : HasInit C),
    @init C hi1 ~~ @init C hi2.
Proof.
  unfold uniquely_isomorphic, isIso.
  intros.
  exists (create (init C)).
  split.
  - exists (create (init C)).
    now split; apply equiv_initial.
  - now intros y _; apply equiv_initial.
Qed.

Lemma HasInit_iso :
  forall (C : Cat) (hi1 hi2 : HasInit C),
    @init C hi1 ~ @init C hi2.
Proof.
  intros. destruct (HasInit_uiso hi1 hi2). cat.
Qed.

Lemma iso_to_init_is_init :
  forall (C : Cat) (hi : HasInit C),
    forall {X : Ob C} (f : Hom X (init C)), isIso f ->
      isInitial C X (fun Y : Ob C => f .> create Y).
Proof.
  intros C hi X f (g & Hfg & Hgf) Y h1 h2.
  now rewrite <- comp_id_l, <- Hfg, comp_assoc, (equiv_initial (g .> h2)),
    <- comp_assoc, Hfg, comp_id_l.
Defined.

Lemma mor_to_init_is_ret :
  forall (C : Cat) (hi : HasInit C) (X : Ob C) (f : Hom X (init C)),
    isRet f.
Proof.
  unfold isRet; intros.
  exists (create X).
  now apply equiv_initial.
Qed.

End wut.