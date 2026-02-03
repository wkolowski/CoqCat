From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal.

Set Implicit Arguments.

Class isZero
  (C : Cat) (Z : Ob C)
  (create : forall X : Ob C, Hom Z X)
  (delete : forall X : Ob C, Hom X Z)
  : Prop :=
{
  isInitial_isZero :: isInitial C Z create;
  isTerminal_isZero :: isTerminal C Z delete;
}.

Definition mediate
  {C : Cat} {Z : Ob C}
  {create : forall X : Ob C, Hom Z X}
  {delete : forall X : Ob C, Hom X Z}
  {isZ : isZero C Z create delete}
  (X Y : Ob C) : Hom X Y :=
    delete X .> create Y.

Class HasZero (C : Cat) : Type :=
{
  HasInit_HasZero :: HasInit C;
  HasTerm_HasZero :: HasTerm C;
  HasZero_spec : init C = term C;
}.

Coercion HasInit_HasZero : HasZero >-> HasInit.
Coercion HasTerm_HasZero : HasZero >-> HasTerm.
