From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal.

Set Implicit Arguments.

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