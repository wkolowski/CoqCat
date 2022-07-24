Require Export ProofIrrelevance FunctionalExtensionality IndefiniteDescription JMeq.
Require Export Setoid Classes.SetoidClass.
Require Export Equality.
Require Export Bool Arith Lia.

Require Export List.
Export ListNotations.

#[global] Set Universe Polymorphism.

(** * Setoids *)

(** Uniqueness up to a custom equivalence relation, using setoids. *)

Definition setoid_unique {A : Type} {S : Setoid A} (P : A -> Prop) (x : A) : Prop :=
  P x /\ (forall y : A, P y -> x == y).

Set Warnings "-deprecated-ident-entry".
Notation "'exists' !! x : A , P" :=
  (ex (@setoid_unique A _ (fun x => P))) (at level 200, x ident).
Set Warnings "+deprecated-ident-entry".

(** Kinds of ordinary functions. The suffix "S" at the end of some
    of these stands for "Setoid". *)

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a = b.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
  injective f /\ surjective f.

Definition injectiveS {A B : Type} {SA : Setoid A} {SB : Setoid B} (f : A -> B) : Prop :=
    forall a a' : A, f a == f a' -> a == a'.

Definition surjectiveS {A B : Type} {S : Setoid B} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a == b.

Definition bijectiveS {A B : Type} {SA : Setoid A} {SB : Setoid B} (f : A -> B) : Prop :=
  injectiveS f /\ surjectiveS f.

Definition surjectiveS'
  {A B : Type} {SA : Setoid A} {SB : Setoid B} (f : A -> B) : Prop :=
    exists g : B -> A,
      Proper (equiv ==> equiv) g /\ forall b : B, f (g b) == b.

#[global] Hint Unfold injective surjective bijective injectiveS surjectiveS bijectiveS : core.

(** Useful automation tactics. *)

Ltac proper :=
match goal with
| |- context [Proper] => unfold Proper, respectful; cbn; intros; proper
| H : ?a == ?b |- _ => rewrite H; clear H; proper
| |- ?a == ?a => reflexivity
| _ => auto
end.

Ltac my_simpl := cbn in *; repeat
match goal with
| H : False |- _ => inversion H
| e : Empty_set |- _ => inversion e
| x : True |- _ => destruct x
| x : unit |- _ => destruct x
| |- context [@eq unit ?a ?b] => destruct a, b
| H : forall _ : unit, _ |- _ => specialize (H tt)
| H : forall _ : True, _ |- _ => specialize (H I)
| H : _ /\ _ |- _ => destruct H
| |- _ /\ _ => split
| |- _ <-> _ => split
| H : exists x, _ |- _ => apply constructive_indefinite_description in H
| H : exists! x, _ |- _ => apply constructive_indefinite_description in H
| H : exists!! x : _, _ |- _ => 
  apply constructive_indefinite_description in H; destruct H; unfold setoid_unique in *
| H : {_ | _} |- _ => destruct H
| H : {_ : _ | _} |- _ => destruct H
| H : {_ : _ & _} |- _ => destruct H
| H : context [setoid_unique] |- _ => red in H
| |- context [setoid_unique] => split
| H : _ = _ |- _ => subst
end.

Ltac solve_equiv := intros; repeat
match goal with
| |- context [Equivalence] => split; red; intros
| |- Reflexive _ => red; intros
| |- Symmetric _ => red; intros
| |- Transitive _ => red; intros
    (* Dealing with equality *)
| |-  ?a = ?a => reflexivity
| H : ?a = ?b |- ?b = ?a => symmetry; assumption
| H : ?a = ?b, H' : ?b = ?c |- ?a = ?c => rewrite H, H'; reflexivity
    (* Quantified equality *)
| H : forall _, ?a _ = ?b _ |- ?b _ = ?a _ => rewrite H; reflexivity
| H : forall _, ?a _ = ?b _, H' : forall _, ?b _ = ?c _
  |- ?a _ = ?c _ => rewrite H, H'; reflexivity
    (* Dealing with setoid equivalence *)
| |-  ?a == ?a => reflexivity
| H : ?a == ?b |- ?b == ?a => symmetry; assumption
| H : ?a == ?b, H' : ?b == ?c |- ?a == ?c => rewrite H, H'; reflexivity
    (* Quantified setoid equivalence *)
| H : forall _, ?a _ == ?b _ |- ?b _ == ?a _ => rewrite H; reflexivity
| H : forall _, ?a _ == ?b _, H' : forall _, ?b _ == ?c _
  |- ?a _ == ?c _ => rewrite H, H'; reflexivity
    (* JMeq *)
| |-  JMeq ?a ?a => reflexivity
| H : JMeq ?a ?b |- JMeq ?b ?a => symmetry; assumption
| H : JMeq ?a ?b, H' : JMeq ?b ?c |- ?a = ?c => rewrite H, H'; reflexivity
| _ => my_simpl; eauto
end.

(** Some setoid instances. *)

#[refine]
#[export]
Instance Setoid_kernel {A B : Type} (f : A -> B) : Setoid A :=
{|
  equiv := fun a a' : A => f a = f a'
|}.
Proof. solve_equiv. Defined.

#[refine]
#[export]
Instance Setoid_kernel_equiv {A B : Type} (S : Setoid B) (f : A -> B) : Setoid A :=
{|
  equiv := fun a a' : A => f a == f a'
|}.
Proof. all: solve_equiv. Defined.

(** Extension of an equivalence relation to a heterogenous equivalence relation.  *)

Inductive JMequiv {A : Type} {S : Setoid A} (x : A) : forall {B : Type}, B -> Prop :=
| JMequiv_refl : forall y : A, x == y -> JMequiv x y.

#[global] Hint Constructors JMequiv : core.

Lemma JMequiv_trans :
  forall (A B C : Type) (SA : Setoid A) (SB : Setoid B) (x : A) (y : B) (z : C),
    A = B -> JMeq SA SB -> JMequiv (S := SA) x y -> JMequiv (S := SB) y z ->
      JMequiv (S := SA) x z.
Proof.
  intros. subst.
  dependent destruction H1.
  dependent destruction H2.
  constructor. rewrite H. assumption.
Qed.

Arguments JMequiv_trans [A B C SA SB x y z] _ _ _ _.

(** Sum-product hybrid. Useful for a few categories that behave like [Rel]. *)

Inductive sumprod (X Y : Set) : Set :=
| inl'  : X -> sumprod X Y
| inr'  : Y -> sumprod X Y
| pair' : X -> Y -> sumprod X Y.

Arguments inl' [X] [Y] _.
Arguments inr' [X] [Y] _.
Arguments pair' [X] [Y] _ _.

#[global] Hint Constructors sumprod : core.

(** Non-empty lists *)

Inductive nel (A : Type) : Type :=
| singl : A -> nel A
| cons_nel : A -> nel A -> nel A.

Arguments singl [A] _.
Arguments cons_nel [A] _ _.

Notation "h ::: t" := (cons_nel h t) (right associativity, at level 30).

Fixpoint nel_app {A : Type} (l1 l2 : nel A) : nel A :=
match l1 with
| singl a => cons_nel a l2
| a ::: l1' => cons_nel a (nel_app l1' l2)
end.

Lemma nel_app_assoc :
  forall (A : Type) (x y z : nel A),
    nel_app x (nel_app y z) = nel_app (nel_app x y) z.
Proof.
  induction x as [h | h t]; cbn; intros.
    trivial.
    rewrite IHt. trivial.
Qed.

Fixpoint nel_map {A B : Type} (f : A -> B) (l : nel A) : nel B :=
match l with
| singl x => singl (f x)
| h ::: t => f h ::: nel_map f t
end.