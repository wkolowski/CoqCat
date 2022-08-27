From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal.

Set Implicit Arguments.

Class isZero
  (C : Cat) (Z : Ob C)
  (create : forall X : Ob C, Hom Z X)
  (delete : forall X : Ob C, Hom X Z)
  : Prop :=
{
  isInitial_isZero :> isInitial Z create;
  isTerminal_isZero :> isTerminal Z delete;
}.

Lemma isZero_Dual :
  forall
    (C : Cat) (X : Ob C)
    (create : forall X' : Ob C, Hom X X')
    (delete : forall X' : Ob C, Hom X' X),
      @isZero (Dual C) X delete create <-> @isZero C X create delete.
Proof. firstorder. Defined.

Class HasZero (C : Cat) : Type :=
{
  zero : Ob C;
  HasZero_HasInit' :> HasInit' zero;
  HasZero_HasTerm' :> HasTerm' zero;
}.

Arguments zero _ {_}.

Coercion HasZero_HasInit' : HasZero >-> HasInit'.
Coercion HasZero_HasTerm' : HasZero >-> HasTerm'.

Definition mediate {C : Cat} {hz : HasZero C} (X Y : Ob C) : Hom X Y :=
  delete X .> create Y.

#[refine]
#[export]
Instance HasTerm_Dual (C : Cat) (hi : HasInit C) : HasTerm (Dual C) :=
{
  term := init C;
}.
Proof.
  esplit. Unshelve. all: cycle 1.
  - exact create.
  - red; cbn; intros; apply create_equiv.
Defined.

#[refine]
#[export]
Instance HasInit_Dual (C : Cat) (ht : HasTerm C) : HasInit (Dual C) :=
{
  init := term C;
}.
Proof.
  esplit. Unshelve. all: cycle 1.
  - exact delete.
  - red; cbn; intros; apply delete_equiv.
Defined.