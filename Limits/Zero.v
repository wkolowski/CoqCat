From Cat Require Export Cat.
From Cat.Limits Require Import Initial Terminal.

Set Implicit Arguments.

Module Traditional.

Definition isZero
  {C : Cat} (Z : Ob C)
  (create : forall X : Ob C, Hom Z X)
  (delete : forall X : Ob C, Hom X Z)
  : Prop := isInitial Z create /\ isTerminal Z delete.

Lemma isZero_Dual :
  forall
    (C : Cat) (X : Ob C)
    (create : forall X' : Ob C, Hom X X')
    (delete : forall X' : Ob C, Hom X' X),
      @isZero (Dual C) X delete create <-> @isZero C X create delete.
Proof. firstorder. Defined.

End Traditional.

Export Traditional.

Class HasZero (C : Cat) : Type :=
{
  HasZero_HasInit :> HasInit C;
  HasZero_HasTerm :> HasTerm C;
  isInitial_isTerminal : init C = term C
}.

Coercion HasZero_HasInit : HasZero >-> HasInit.
Coercion HasZero_HasTerm : HasZero >-> HasTerm.

#[global] Hint Resolve isInitial_isTerminal : core.

#[refine]
#[export]
Instance HasZero_Dual (C : Cat) (hz : HasZero C) : HasZero (Dual C) :=
{
  HasZero_HasInit := HasInit_Dual hz;
  HasZero_HasTerm := HasTerm_Dual hz;
}.
Proof. cat. Defined.