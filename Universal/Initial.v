From Cat Require Export Cat.

Set Implicit Arguments.

Class isInitial {C : Cat} (I : Ob C) (create : forall X : Ob C, Hom I X) : Prop :=
  create_equiv : forall {X : Ob C} (f g : Hom I X), f == g.

Arguments create_equiv {C I create isInitial X f} _.

Class HasInit' {C : Cat} (I : Ob C) : Type :=
{
  create : forall X : Ob C, Hom I X;
  HasInit'_isInitial :> isInitial I create;
}.

Arguments create {C _ _} _.

Coercion HasInit'_isInitial : HasInit' >-> isInitial.

Class HasInit (C : Cat) : Type :=
{
  init : Ob C;
  HasInit_HasInit' :> HasInit' init;
}.

Arguments init _ {_}.

Coercion HasInit_HasInit' : HasInit >-> HasInit'.

Lemma isInitial_uiso :
  forall
    (C : Cat)
    (I1 : Ob C) (create1 : forall X : Ob C, Hom I1 X)
    (I2 : Ob C) (create2 : forall X : Ob C, Hom I2 X),
      isInitial I1 create1 ->
      isInitial I2 create2 ->
        I1 ~~ I2.
Proof.
  intros C I1 create1 I2 create2 H1 H2.
  exists (create1 I2).
  split.
  - exists (create2 I1).
    split; apply create_equiv.
  - now intros; apply create_equiv.
Qed.

Lemma isInitial_iso :
  forall
    (C : Cat)
    (I1 : Ob C) (create1 : forall X : Ob C, Hom I1 X)
    (I2 : Ob C) (create2 : forall X : Ob C, Hom I2 X),
      isInitial I1 create1 ->
      isInitial I2 create2 ->
        I1 ~ I2.
Proof.
  intros. destruct (isInitial_uiso H H0). cat.
Qed.

Lemma isInitial_create_equiv :
  forall
    (C : Cat)
    (I : Ob C) (create1 create2 : forall X : Ob C, Hom I X),
      isInitial I create1 ->
      isInitial I create2 ->
        forall X : Ob C, create1 X == create2 X.
Proof.
  now intros; apply create_equiv.
Qed.

Lemma iso_to_init_is_init :
  forall (C : Cat) (I : Ob C) (create : forall X : Ob C, Hom I X),
    isInitial I create ->
      forall {X : Ob C} (f : Hom X I), isIso f ->
        isInitial X (fun Y : Ob C => f .> create Y).
Proof.
  intros C I c H X f (f' & Heq1 & Heq2) Y g1 g2.
  now rewrite <- comp_id_l, <- Heq1, comp_assoc, (create_equiv (f' .> g2)),
    <- comp_assoc, Heq1, comp_id_l.
Defined.

Lemma mor_to_init_is_ret :
  forall (C : Cat) (I : Ob C) (create : forall X : Ob C, Hom I X),
    isInitial I create ->
      forall {X : Ob C} (f : Hom X I), isRet f.
Proof.
  unfold isRet; intros.
  exists (create0 X).
  apply create_equiv.
Qed.