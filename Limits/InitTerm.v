From Cat Require Export Cat.

Set Implicit Arguments.

Class HasInit (C : Cat) : Type :=
{
  init : Ob C;
  create : forall X : Ob C, Hom init X;
  create_unique : forall [X : Ob C] (f : Hom init X), f == create X;
}.

Arguments init   _ {_}.
Arguments create {C _ } _.

Ltac init := intros; repeat
match goal with
| |- context [?f] =>
  match type of f with
  | Hom (init _) _ => rewrite (create_unique f)
  end
| |- ?x == ?x => reflexivity
end; try (cat; fail).

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  delete : forall X : Ob C, Hom X term;
  delete_unique : forall [X : Ob C] (f : Hom X term), f == delete X;
}.

Arguments term   _ {_}.
Arguments delete {C _} _.

Ltac term := intros; repeat
match goal with
| |- context [?f] =>
  match type of f with
  | Hom _ (term _) => rewrite (delete_unique f)
  end
| |- ?x == ?x => reflexivity
end; try (cat; fail).

Class HasZero (C : Cat) : Type :=
{
  HasZero_HasInit :> HasInit C;
  HasZero_HasTerm :> HasTerm C;
  initial_is_terminal : init C = term C
}.

Coercion HasZero_HasInit : HasZero >-> HasInit.
Coercion HasZero_HasTerm : HasZero >-> HasTerm.

#[global] Hint Resolve create_unique delete_unique initial_is_terminal : core.

#[refine]
#[export]
Instance HasTerm_Dual (C : Cat) (hi : HasInit C) : HasTerm (Dual C) :=
{
  term := init C;
  delete := @create C hi
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

#[refine]
#[export]
Instance HasZero_Dual (C : Cat) (hz : HasZero C) : HasZero (Dual C) :=
{
  HasZero_HasInit := HasInit_Dual hz;
  HasZero_HasTerm := HasTerm_Dual hz;
}.
Proof. cat. Defined.

Module Equational.

(* Lemmas ported from InitTerm.v *)

Lemma HasInit_uiso :
  forall (C : Cat) (hi1 hi2 : HasInit C),
    @init C hi1 ~~ @init C hi2.
Proof.
  intros.
  red. exists (create (init C)). red. split.
    red. exists (create (init C)). split;
      rewrite create_unique, (create_unique (id (init C)));
        reflexivity.
    destruct hi1, hi2. intros. cbn. rewrite (create_unique0 _ y).
      cbn. reflexivity.
Qed.

Lemma HasTerm_uiso :
  forall (C : Cat) (ht1 ht2 : HasTerm C),
    @term C ht1 ~~ @term C ht2.
Proof.
  intros.
  red. exists (delete (term C)). red. split.
    red. exists (delete (term C)). split;
      rewrite delete_unique, (delete_unique (id (term C)));
        reflexivity.
    destruct ht1, ht2. intros. cbn. rewrite (delete_unique1 _ y).
      cbn. reflexivity.
Qed.

(*
Lemma iso_to_init_is_init :
  forall (C : Cat) (I X : Ob C) (create : forall I' : Ob C, Hom I I'),
    initial I create -> forall f : Hom X I, Iso f ->
      initial X (fun X' : Ob C => f .> create X').
Proof.
  repeat split; intros. iso.
  edestruct H. rewrite (H1 (f_inv .> y)). cat.
    assocl. rewrite f_inv_eq1. cat.
    trivial.
Defined.

Lemma iso_to_term_is_term : 
  forall (C : Cat) (X T : Ob C) (delete : forall T' : Ob C, Hom T' T),
    terminal T delete -> forall f : Hom T X, Iso f ->
      terminal X (fun X' : Ob C => delete X' .> f).
Proof.
  repeat split; intros. iso.
  edestruct H. rewrite (H1 (y .> f_inv)).
    assocr. rewrite f_inv_eq2. cat.
    trivial.
Defined.
*)

Lemma mor_to_init_is_ret :
  forall (C : Cat) (hi : HasInit C) (X : Ob C) (f : Hom X (init C)),
    Ret f.
Proof.
  intros. red. exists (create X).
  rewrite !create_unique.
  destruct hi. rewrite <- create_unique0. reflexivity.
Qed.

Lemma mor_from_term_is_sec :
  forall (C : Cat) (ht : HasTerm C) (X : Ob C) (f : Hom (term C) X),
    Sec f.
Proof.
  intros. red. exists (delete X).
  rewrite !delete_unique.
  destruct ht. rewrite <- delete_unique0. reflexivity.
Qed.

End Equational.

Definition initial
  {C : Cat} (I : Ob C) (create : forall X : Ob C, Hom I X) : Prop :=
    forall X : Ob C, setoid_unique (fun _ => True) (create X).

Definition terminal
  {C : Cat} (T : Ob C) (delete : forall X : Ob C, Hom X T) : Prop :=
    forall X : Ob C, setoid_unique (fun _ => True) (delete X).

Definition isZero
  {C : Cat} (Z : Ob C)
  (create : forall X : Ob C, Hom Z X)
  (delete : forall X : Ob C, Hom X Z)
  : Prop := initial Z create /\ terminal Z delete.

Lemma dual_initial_terminal :
  forall (C : Cat) (X : Ob C) (create : forall X' : Ob C, Hom X X'),
    @initial C X create <-> @terminal (Dual C) X create.
Proof. cat. Qed.

Lemma dual_zero_self :
  forall
    (C : Cat) (X : Ob C)
    (create : forall X' : Ob C, Hom X X')
    (delete : forall X' : Ob C, Hom X' X),
      @isZero C X create delete <-> @isZero (Dual C) X delete create.
Proof.
  unfold isZero; cat.
Qed.

Lemma initial_uiso :
  forall
    (C : Cat) (A B : Ob C)
    (create : forall X : Ob C, Hom A X)
    (create' : forall X : Ob C, Hom B X),
      initial A create -> initial B create' -> A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic; intros.
  red in H. red in H0.
  destruct (H B) as [_ Hf], (H0 A) as [_ Hg], (H A) as [_ HA], (H0 B) as [_ HB].
  exists (create0 B); red. split; auto. exists (create' A); split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Qed.

Lemma initial_iso :
  forall
    (C : Cat) (A B : Ob C)
    (create : forall X : Ob C, Hom A X)
    (create' : forall X : Ob C, Hom B X),
      initial A create -> initial B create' -> A ~ B.
Proof.
  intros. destruct (initial_uiso H H0). cat.
Qed.

Lemma initial_create_equiv :
  forall
    (C : Cat) (I : Ob C)
    (create : forall X : Ob C, Hom I X)
    (create' : forall X : Ob C, Hom I X),
      initial I create -> initial I create' ->
        forall X : Ob C, create X == create' X.
Proof.
  intros. edestruct H. apply H2. trivial.
Qed.

Lemma terminal_uiso :
  forall
    (C : Cat) (A B : Ob C)
    (delete : forall X : Ob C, Hom X A)
    (delete' : forall X : Ob C, Hom X B),
      terminal A delete -> terminal B delete' -> A ~~ B.
Proof.
  intro C. rewrite <- (Dual_Dual C); cbn; intros.
  rewrite <- dual_initial_terminal in *.
  rewrite dual_unique_iso_self.
  eapply initial_uiso; cat.
Qed.

Lemma terminal_iso :
  forall
    (C : Cat) (A B : Ob C)
    (delete : forall X : Ob C, Hom X A)
    (delete' : forall X : Ob C, Hom X B),
      terminal A delete -> terminal B delete' -> A ~ B.
Proof.
  intros. destruct (terminal_uiso H H0). cat.
Qed.

Lemma terminal_delete_equiv :
  forall
    (C : Cat) (T : Ob C)
    (delete : forall X : Ob C, Hom X T)
    (delete' : forall X : Ob C, Hom X T),
      terminal T delete -> terminal T delete' ->
        forall X : Ob C, delete X == delete' X.
Proof.
  intros. edestruct H. apply H2. trivial.
Qed.

Lemma iso_to_init_is_init :
  forall (C : Cat) (I X : Ob C) (create : forall I' : Ob C, Hom I I'),
    initial I create -> forall f : Hom X I, Iso f ->
      initial X (fun X' : Ob C => f .> create X').
Proof.
  repeat split; intros. iso.
  edestruct H. rewrite (H1 (f_inv .> y)). cat.
    assocl. rewrite f_inv_eq1. cat.
    trivial.
Defined.

Lemma iso_to_term_is_term : 
  forall (C : Cat) (X T : Ob C) (delete : forall T' : Ob C, Hom T' T),
    terminal T delete -> forall f : Hom T X, Iso f ->
      terminal X (fun X' : Ob C => delete X' .> f).
Proof.
  repeat split; intros. iso.
  edestruct H. rewrite (H1 (y .> f_inv)).
    assocr. rewrite f_inv_eq2. cat.
    trivial.
Defined.

Lemma mor_to_init_is_ret :
  forall (C : Cat) (I X : Ob C) (f : Hom X I) (create : forall I' : Ob C, Hom I I'),
    initial I create -> Ret f.
Proof.
  intros. red. exists (create0 X).
  edestruct H. rewrite <- H1; cat.
Qed.

Lemma mor_from_term_is_sec :
  forall (C : Cat) (T X : Ob C) (f : Hom T X) (delete : forall T' : Ob C, Hom T' T),
    terminal T delete -> Sec f.
Proof.
  intros. red. exists (delete0 X).
  edestruct H. rewrite <- H1; cat.
Qed.