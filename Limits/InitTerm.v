From Cat Require Export Cat.

Set Implicit Arguments.

Definition initial
  {C : Cat} (I : Ob C) (create : forall X : Ob C, Hom I X) : Prop :=
    forall X : Ob C, setoid_unique (fun _ => True) (create X).

Definition terminal
  {C : Cat} (T : Ob C) (delete : forall X : Ob C, Hom X T) : Prop :=
    forall X : Ob C, setoid_unique (fun _ => True) (delete X).

Definition zero
  {C : Cat} (Z : Ob C)
  (create : forall X : Ob C, Hom Z X)
  (delete : forall X : Ob C, Hom X Z)
  : Prop := initial Z create /\ terminal Z delete.

Class HasInit (C : Cat) : Type :=
{
  init : Ob C;
  create : forall X : Ob C, Hom init X;
  is_initial : forall (X : Ob C) (f : Hom init X), f == create X
}.

Arguments init   _ {_}.
Arguments create {C _ } _.

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  delete : forall X : Ob C, Hom X term;
  is_terminal : forall (X : Ob C) (f : Hom X term), f == delete X
}.

Arguments term   _ {_}.
Arguments delete {C _} _.

Class HasZero (C : Cat) : Type :=
{
  zero_is_initial :> HasInit C;
  zero_is_terminal :> HasTerm C;
  initial_is_terminal : init C = term C
}.

Coercion zero_is_initial : HasZero >-> HasInit.
Coercion zero_is_terminal : HasZero >-> HasTerm.

#[global] Hint Resolve is_initial is_terminal initial_is_terminal unique_iso_is_iso : core.

#[refine]
#[export]
Instance Dual_HasTerm (C : Cat) (hi : HasInit C) : HasTerm (Dual C) :=
{
  term := init C;
  delete := @create C hi
}.
Proof. cat. Defined.

#[refine]
#[export]
Instance Dual_HasInit (C : Cat) (ht : HasTerm C) : HasInit (Dual C) :=
{
  init := term C;
  create := @delete C ht
}.
Proof. cat. Defined.

#[refine]
#[export]
Instance Dual_HasZero (C : Cat) (hz : HasZero C) : HasZero (Dual C) :=
{
  zero_is_initial := Dual_HasInit hz;
  zero_is_terminal := Dual_HasTerm hz
}.
Proof. cat. Defined.

Definition zero_ob (C : Cat) {hz : HasZero C} : Ob C := init C.
Definition zero_mor (C : Cat) {hz : HasZero C} (X Y : Ob C) : Hom X Y.
Proof.
  pose (f := delete X). pose (g := create Y).
  rewrite initial_is_terminal in g. exact (f .> g).
Defined.

Ltac init := intros; repeat
match goal with
| |- context [?f] =>
  match type of f with
  | Hom (init _) _ => rewrite (is_initial _ f)
  end
| |- ?x == ?x => reflexivity
end; try (cat; fail).

Ltac term := intros; repeat
match goal with
| |- context [?f] =>
  match type of f with
  | Hom _ (term _) => rewrite (is_terminal _ f)
  end
| |- ?x == ?x => reflexivity
end; try (cat; fail).

Lemma dual_initial_terminal :
  forall (C : Cat) (X : Ob C) (create : forall X' : Ob C, Hom X X'),
    @initial C X create <-> @terminal (Dual C) X create.
Proof. cat. Qed.

Lemma dual_zero_self :
  forall
    (C : Cat) (X : Ob C)
    (create : forall X' : Ob C, Hom X X')
    (delete : forall X' : Ob C, Hom X' X),
      @zero C X create delete <-> @zero (Dual C) X delete create.
Proof.
  unfold zero; cat.
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