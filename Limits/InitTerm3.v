From Cat Require Export Cat.

Set Implicit Arguments.

Class HasInit' {C : Cat} (I : Ob C) : Type :=
{
  create : forall X : Ob C, Hom I X;
  create_unique : forall {X : Ob C} (f : Hom I X), f == create X
}.

Arguments create {C _ _} _.

Class HasInit (C : Cat) : Type :=
{
  init : Ob C;
  HasInit_HasInit' :> HasInit' init;
}.

Arguments init _ {_}.

Coercion HasInit_HasInit' : HasInit >-> HasInit'.

Ltac init := intros; repeat
match goal with
| _ : HasInit' ?I |- context [?f] =>
  match type of f with
  | Hom I _ => rewrite (create_unique f)
  end
| |- context [?f] =>
  match type of f with
  | Hom (init _) _ => rewrite (create_unique f)
  end
| |- ?x == ?x => reflexivity
end; try (cat; fail).

Class HasTerm' {C : Cat} (T : Ob C) : Type :=
{
  delete : forall X : Ob C, Hom X T;
  delete_unique : forall {X : Ob C} (f : Hom X T), f == delete X
}.

Arguments delete {C _ _} _.

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  HasTerm_HasTerm' :> HasTerm' term;
}.

Arguments term _ {_}.

Coercion HasTerm_HasTerm' : HasTerm >-> HasTerm'.

Ltac term := intros; repeat
match goal with
| _ : HasTerm' ?T |- context [?f] =>
  match type of f with
  | Hom _ T => rewrite (delete_unique f)
  end
| |- context [?f] =>
  match type of f with
  | Hom _ (term _) => rewrite (delete_unique f)
  end
| |- ?x == ?x => reflexivity
end; try (cat; fail).

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
  esplit. Unshelve. all: cycle 1; cbn.
  - exact create.
  - intros. init.
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
  - intros. term.
Defined.

(*
Lemma dual_initial_terminal :
  forall (C : Cat) (X : Ob C) (create : forall X' : Ob C, Hom X X'),
    @initial C X create <-> @terminal (Dual C) X create.
Proof. cat. Qed.
*)

(* Lemma dual_zero_self :
  forall
    (C : Cat) (X : Ob C)
    (create : forall X' : Ob C, Hom X X')
    (delete : forall X' : Ob C, Hom X' X),
      @isZero C X create delete <-> @isZero (Dual C) X delete create.
Proof.
  unfold isZero; cat.
Qed.
 *)

Lemma HasInit'_uiso :
  forall
    (C : Cat)
    (I1 : Ob C) (hi1 : HasInit' I1)
    (I2 : Ob C) (hi2 : HasInit' I2),
      I1 ~~ I2.
Proof.
  unfold uniquely_isomorphic, isomorphic.
  intros.
  exists (create I2).
  split.
  - unfold isIso.
    exists (create I1).
    init.
  - intros. init.
Qed.

Lemma initial_iso :
  forall
    (C : Cat)
    (I1 : Ob C) (hi1 : HasInit' I1)
    (I2 : Ob C) (hi2 : HasInit' I2),
      I1 ~ I2.
Proof.
  intros. destruct (HasInit'_uiso hi1 hi2). cat.
Qed.

Lemma initial_create_equiv :
  forall (C : Cat) (I : Ob C) (hi1 hi2 : HasInit' I),
    forall X : Ob C, @create _ _ hi1 X == @create _ _ hi2 X.
Proof.
  intros.
  apply create_unique.
Qed.

Lemma iso_to_init_is_init :
  forall (C : Cat) (I X : Ob C),
    Iso I X -> HasInit' I -> HasInit' X.
Proof.
  intros C I X (f & g) hi.
(*   intros C I c H X f (f' & Heq1 & Heq2) Y g.
  rewrite <- (H _ (f' .> g)), <- comp_assoc, Heq1, comp_id_l.
  reflexivity. *)
Admitted.

Lemma mor_to_init_is_ret :
  forall (C : Cat) (hi : HasInit C),
    forall {X : Ob C} (f : Hom X (init C)), isRet f.
Proof.
  unfold isRet.
  intros.
  exists (create X).
  init.
Qed.

Lemma HasTerm'_uiso :
  forall
    (C : Cat)
    (T1 : Ob C) (ht1 : HasTerm' T1)
    (T2 : Ob C) (ht2 : HasTerm' T2),
      T1 ~~ T2.
Proof.
  unfold uniquely_isomorphic, isomorphic.
  intros.
  exists (delete T1).
  split.
  - unfold isIso.
    exists (delete T2).
    term.
  - intros. term.
Qed.

Lemma HasTerm'_iso :
  forall
    (C : Cat)
    (T1 : Ob C) (ht1 : HasTerm' T1)
    (T2 : Ob C) (ht2 : HasTerm' T2),
      T1 ~ T2.
Proof.
  intros. destruct (HasTerm'_uiso ht1 ht2). cat.
Qed.

Lemma terminal_delete_equiv :
  forall (C : Cat) (T : Ob C) (ht1 ht2 : HasTerm' T),
    forall X : Ob C, @delete _ _ ht1 X == @delete _ _ ht2 X.
Proof.
  intros.
  apply delete_unique.
Qed.

Lemma iso_to_term_is_term :
  forall (C : Cat) (T X : Ob C),
    T ~ X -> HasTerm' T -> HasTerm' X.
Proof.
  intros C T X HIso ht.
(*   intros C I c H X f (f' & Heq1 & Heq2) Y g.
  rewrite <- (H _ (f' .> g)), <- comp_assoc, Heq1, comp_id_l.
  reflexivity. *)
Admitted.

Lemma mor_from_term_is_sec :
  forall (C : Cat) (ht : HasTerm C),
    forall {X : Ob C} (f : Hom (term C) X), isSec f.
Proof.
  unfold isSec.
  intros.
  exists (delete X).
  term.
Qed.