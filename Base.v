Require Export Coq.Classes.SetoidClass.

(*Require Export Coq.Logic.ProofIrrelevance.*)
(*Require Export Coq.Logic.FunctionalExtensionality.*)
Require Export Coq.Logic.IndefiniteDescription.

Require Export JMeq.

Global Set Universe Polymorphism.

Inductive extEq : forall A : Type, A -> A -> Prop :=
    | extEq_refl : forall (A : Type) (x (*y*) : A), (*x = y ->*) extEq A x x
    | extEq_sym : forall (A : Type) (x y : A), extEq A x y -> extEq A y x
    | extEq_trans : forall (A : Type) (x y z : A),
      extEq A x y -> extEq A y z -> extEq A x z
    | extEq_ext : forall (A B : Type) (f g : A -> B),
      (forall a : A, extEq B (f a) (g a)) -> extEq (A -> B) f g
    | extEq_unext : forall (A B : Type) (f g : A -> B),
      extEq (A -> B) f g -> forall x y : A, extEq A x y ->
      extEq B (f x) (g y).

Arguments extEq [A] _ _.

Hint Constructors extEq.

Instance extEq_Equivalence (A : Type) : Equivalence (@extEq A).
Proof. split; eauto. Defined.

Instance extEq_Proper : forall (A B : Type) (f : A -> B),
    Proper (@extEq A ==> @extEq B) f.
Proof.
  repeat red; intros. induction H; subst.
    auto.
    eapply extEq_trans; eauto.
    eapply extEq_trans; eauto.
    apply extEq_unext; auto.
    apply extEq_unext; auto.
Defined.

Instance extEq_Proper' : forall (A B : Type) (f : A -> B),
    Proper (@extEq A --> @extEq B) f.
Proof.
  repeat red; intros. induction H; subst.
    auto.
    eapply extEq_trans; eauto.
    eapply extEq_trans; eauto.
    apply extEq_unext; auto.
    apply extEq_unext; auto.
Defined.

Instance extEq_Proper'' : forall (A : Type),
    Proper (@extEq A ==> @extEq A ==> (Basics.flip Basics.impl)) (@extEq A).
Proof.
  repeat red. intros. eapply extEq_trans. eauto. eauto.
Defined.

Inductive depExtEq : forall A B : Type, A -> B -> Prop :=
    | depExtEq_eq : forall (A : Type) (x y : A), x = y -> depExtEq A A x y
    | depExtEq_sym : forall (A B : Type) (x : A) (y : B),
      depExtEq A B x y -> depExtEq B A y x
    | depExtEq_trans : forall (A B C : Type) (x : A) (y : B) (z : C),
      depExtEq A B x y -> depExtEq B C y z -> depExtEq A C x z
    | depExtEq_ext : forall (A : Type) (B C : A -> Type)
      (f : forall x : A, B x) (g : forall x : A, C x),
      (forall x : A, depExtEq (B x) (C x) (f x) (g x)) ->
      depExtEq (forall x : A, B x) (forall x : A, C x) f g
    | depExtEq_unext :
      forall (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type)
      (f : forall x : A1, B1 x) (g : forall x : A2, B2 x),
      depExtEq (forall x : A1, B1 x) (forall x : A2, B2 x) f g ->
      forall (x : A1) (y : A2), depExtEq A1 A2 x y ->
      depExtEq (B1 x) (B2 y) (f x) (g y).

Arguments depExtEq [A B] _ _.
Arguments depExtEq_eq [A x y] _.
Arguments depExtEq_ext [A B C] _ _ _.
Arguments depExtEq_unext [A1 A2 B1 B2] _ _ _ _ _ _.

Hint Constructors depExtEq.

Instance depExtEq_Equivalence (A : Type) : Equivalence (@depExtEq A A).
Proof.
  split; red; simpl; intros; eauto.
Defined.

Ltac solve_depExtEq := repeat
match goal with
    | |- depExtEq (fun _ => _) _ => apply depExtEq_ext; intro
    | |- depExtEq _ (fun _ => _) => apply depExtEq_ext; intro
end; auto;
repeat (auto; match goal with
    | |- depExtEq (fun _ => _) (fun _ => _) => apply depExtEq_ext; intro
    | H : depExtEq ?f ?g |- depExtEq (?f _ _ _) (?g _ _ _) =>
      apply (depExtEq_unext (f _ _) (g _ _))
    | H : depExtEq ?f ?g |- depExtEq (?f _ _) (?g _ _) =>
      apply (depExtEq_unext (f _) (g _))
    | H : depExtEq ?f ?g |- depExtEq (?f _) (?g _) => 
      apply (depExtEq_unext f g)
    | |- depExtEq (?f _ _) (?f _ _) => apply (depExtEq_unext (f _) (f _))
    | |- depExtEq (?f _) (?f _) => apply (depExtEq_unext f f)
    | |- depExtEq (_, _) ?x => rewrite (surjective_pairing x)
end); auto.

Instance depExtEq_Proper : forall (A B : Type) (f : A -> B),
    Proper (@depExtEq A A ==> @depExtEq B B) f.
Proof.
  unfold Proper, respectful; intros. solve_depExtEq. (*
  apply (depExtEq_unext f f); auto.*)
Qed.

Instance depExtEq_Proper' : forall (A : Type),
    Proper (@depExtEq A A ==> @depExtEq A A ==>
      (Basics.flip Basics.impl)) (@depExtEq A A).
Proof.
  repeat red. intros. eapply depExtEq_trans; eauto.
Defined.

Inductive sumprod (X Y : Set) : Set :=
    | inl' : X -> sumprod X Y
    | inr' : Y -> sumprod X Y
    | pair' : X -> Y -> sumprod X Y.

Arguments inl' [X] [Y] _.
Arguments inr' [X] [Y] _.
Arguments pair' [X] [Y] _ _.

Hint Constructors sumprod.

(* Moved here so that tactics work *)
Definition setoid_unique {A : Type} {S : Setoid A} (P : A -> Prop) (x : A)
    : Prop := P x /\ (forall y : A, P y -> x == y).

Notation "'exists' !! x : A , P" :=
    (ex (@setoid_unique A _ (fun x => P))) (at level 200, x ident).

(* Kinds of ordinary functions. The suffix "S" at the end of some
   of these stands for "Setoid". *)
Definition injective {A B : Type} (f : A -> B) : Prop :=
    forall x y : A, f x = f y -> x = y.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
    forall b : B, exists a : A, f a = b.

Definition bijective {A B : Type} (f : A -> B) : Prop :=
    injective f /\ surjective f.

Definition injectiveS {A B : Type} {SA : Setoid A} {SB : Setoid B}
    (f : A -> B) : Prop := forall a a' : A, f a == f a' -> a == a'.

Definition surjectiveS {A B : Type} {S : Setoid B} (f : A -> B) : Prop :=
    forall b : B, exists a : A, f a == b.

Definition bijectiveS {A B : Type} {SA : Setoid A} {SB : Setoid B}
    (f : A -> B) : Prop := injectiveS f /\ surjectiveS f.

Hint Unfold
    injective surjective bijective
    injectiveS surjectiveS bijectiveS.

Ltac proper :=
match goal with
    | |- context [Proper] => unfold Proper, respectful; simpl; intros; proper
    | H : ?a == ?b |- _ => rewrite H; clear H; proper
    | |- ?a == ?a => reflexivity
    | _ => auto
end.

Ltac my_simpl := simpl in *; repeat
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
    | H : exists x, _ |- _ =>
      apply constructive_indefinite_description in H
    | H : exists! x, _ |- _ =>
      apply constructive_indefinite_description in H
    | H : exists!! x : _, _ |- _ => 
      apply constructive_indefinite_description in H;
        destruct H; unfold setoid_unique in *
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

#[refine]
Instance Setoid_kernel {A B : Type} (f : A -> B) : Setoid A :=
    {| equiv := fun a a' : A => f a = f a' |}.
Proof. solve_equiv. Defined.

#[refine]
Instance Setoid_kernel_equiv {A B : Type} (S : Setoid B) (f : A -> B)
    : Setoid A := {| equiv := fun a a' : A => f a == f a' |}.
Proof. all: solve_equiv. Defined.

Inductive JMequiv {A : Type} {is_setoid : Setoid A} (x : A)
    : forall {B : Type}, B -> Prop :=
    | JMequiv_refl : forall y : A, x == y -> JMequiv x y.

Hint Constructors JMequiv.

Theorem eta : forall (A B : Type) (f : A -> B),
    f = fun x : A => f x.
Proof. trivial. Qed.

(* Relation classes *)

Class MyReflexive {A : Type} (R : A -> A -> Prop) : Prop :=
{
    reflexive : forall x : A, R x x;
}.

Class MySymmetric {A : Type} (R : A -> A -> Prop) : Prop :=
{
    symmetric : forall x y : A, R x y -> R y x;
}.

Class MyTransitive {A : Type} (R : A -> A -> Prop) : Prop :=
{
    transitive : forall x y z : A, R x y -> R y z -> R x z;
}.

Class Dense {A : Type} (R : A -> A -> Prop) : Prop :=
{
    dense : forall x y : A, R x y -> exists z : A, R x z /\ R z y
}.

Class Antireflexive {A : Type} (R : A -> A -> Prop) : Prop :=
{
    irreflexive : forall x : A, ~ R x x;
}.

Class MyAntisymmetric {A : Type} (R : A -> A -> Prop) : Prop :=
{
    antisymmetric : forall x y : A, R x y -> ~ R y x;
}.