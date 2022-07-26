From Cat Require Export Cat.

Set Implicit Arguments.

Class isInitial {C : Cat} (I : Ob C) (create : forall X : Ob C, Hom I X) : Prop :=
  isInitial' : forall {X : Ob C} (f : Hom I X), f == create X.

Class isTerminal {C : Cat} (T : Ob C) (delete : forall X : Ob C, Hom X T) : Prop :=
  isTerminal' : forall {X : Ob C} (f : Hom X T), f == delete X.

Class HasInit' {C : Cat} (I : Ob C) : Type :=
{
  create : forall X : Ob C, Hom I X;
  HasInit'_isInitial :> isInitial I create;
}.

Coercion HasInit'_isInitial : HasInit' >-> isInitial.

Class HasTerm' {C : Cat} (T : Ob C) : Type :=
{
  delete : forall X : Ob C, Hom X T;
  HasTerm'_isTerminal :> isTerminal T delete;
}.

Coercion HasTerm'_isTerminal : HasTerm' >-> isTerminal.

Class HasInit (C : Cat) : Type :=
{
  init : Ob C;
  HasInit_HasInit' :> HasInit' init;
}.

Coercion HasInit_HasInit' : HasInit >-> HasInit'.

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  HasTerm_HasTerm' :> HasTerm' term;
}.

Coercion HasTerm_HasTerm' : HasTerm >-> HasTerm'.

Class HasZero (C : Cat) : Type :=
{
  zero : Ob C;
  HasZero_HasInit' :> HasInit' zero;
  HasZero_HasTerm' :> HasTerm' zero;
}.

Coercion HasZero_HasInit' : HasZero >-> HasInit'.
Coercion HasZero_HasTerm' : HasZero >-> HasTerm'.

#[global] Hint Unfold isInitial' isTerminal' isInitial isTerminal : core.
(*
#[refine]
#[export]
Instance HasTerm_Dual (C : Cat) (hi : HasInit C) : HasTerm (Dual C) :=
{
  term := init C;
(*   delete := @create C hi *)
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
*)