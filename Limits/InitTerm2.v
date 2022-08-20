From Cat Require Export Cat.

Set Implicit Arguments.

Class isInitial {C : Cat} (I : Ob C) (create : forall X : Ob C, Hom I X) : Prop :=
  create_unique : forall {X : Ob C} (f : Hom I X), f == create X.

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

Class isTerminal {C : Cat} (T : Ob C) (delete : forall X : Ob C, Hom X T) : Prop :=
  delete_unique : forall {X : Ob C} (f : Hom X T), f == delete X.

Class HasTerm' {C : Cat} (T : Ob C) : Type :=
{
  delete : forall X : Ob C, Hom X T;
  HasTerm'_isTerminal :> isTerminal T delete;
}.

Arguments delete {C _ _} _.

Coercion HasTerm'_isTerminal : HasTerm' >-> isTerminal.

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  HasTerm_HasTerm' :> HasTerm' term;
}.

Arguments term _ {_}.

Coercion HasTerm_HasTerm' : HasTerm >-> HasTerm'.

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

#[global] Hint Unfold create_unique delete_unique isInitial isTerminal : core.

#[refine]
#[export]
Instance HasTerm_Dual (C : Cat) (hi : HasInit C) : HasTerm (Dual C) :=
{
  term := init C;
}.
Proof.
  esplit. Unshelve. all: cycle 1; cbn.
  - exact create.
  - unfold isTerminal; cbn. intros. rewrite create_unique. reflexivity.
Defined.

#[refine]
#[export]
Instance HasInit_Dual (C : Cat) (ht : HasTerm C) : HasInit (Dual C) :=
{
  init := term C;
}.
Proof.
  esplit. Unshelve. all: cycle 1; cbn.
  - exact delete.
  - unfold isInitial; cbn. intros. rewrite delete_unique. reflexivity.
Defined.