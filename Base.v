Require Export Coq.Classes.SetoidClass.

(*Require Export Coq.Logic.ProofIrrelevance.*)
(*Require Export Coq.Logic.FunctionalExtensionality.*)
Require Export Coq.Logic.IndefiniteDescription.

Require Export JMeq.

Global Set Universe Polymorphism.

Inductive extEq : forall A : Set, A -> A -> Prop :=
    (* TODO: change this from _refl to _eq so that shit is easier
      and you don't need to destruct equalities. This will affect
      equalizers in ExtSet.v *)
    | extEq_refl : forall (A : Set) (x : A), extEq A x x
    | extEq_sym : forall (A : Set) (x y : A), extEq A x y -> extEq A y x
    | extEq_trans : forall (A : Set) (x y z : A),
      extEq A x y -> extEq A y z -> extEq A x z
    | extEq_ext : forall (A B : Set) (f g : A -> B),
      (forall a : A, extEq B (f a) (g a)) -> extEq (A -> B) f g
    | extEq_unext : forall (A B : Set) (f g : A -> B),
      extEq (A -> B) f g -> forall x y : A, extEq A x y ->
      extEq B (f x) (g y).

Arguments extEq [A] _ _.

Hint Constructors extEq.

Instance extEq_Equivalence (A : Set) : Equivalence (@extEq A).
Proof. split; eauto. Defined.

Theorem extEq_Proper : forall (A B : Set) (f : A -> B),
    Proper (@extEq A ==> @extEq B) f.
Proof.
  repeat red; intros. induction H; subst.
    auto.
    eapply extEq_trans; eauto.
    eapply extEq_trans; eauto.
    apply extEq_unext; auto.
    apply extEq_unext; auto.
Defined.

Theorem extEq_Proper' : forall (A B : Set) (f : A -> B),
    Proper (@extEq A --> @extEq B) f.
Proof.
  repeat red; intros. induction H; subst.
    auto.
    eapply extEq_trans; eauto.
    eapply extEq_trans; eauto.
    apply extEq_unext; auto.
    apply extEq_unext; auto.
Defined.

Theorem extEq_Proper'' : forall (A : Set),
    Proper (@extEq A ==> @extEq A ==> (Basics.flip Basics.impl)) (@extEq A).
Proof.
  repeat red. intros. eapply extEq_trans. eauto. eauto.
Defined.

Inductive etaEq : forall A : Set, A -> A -> Prop :=
    | etaEq_refl : forall (A : Set) (x : A), etaEq A x x
    | etaEq_sym : forall (A : Set) (x y : A), etaEq A x y -> etaEq A y x
    | etaEq_trans : forall (A : Set) (x y z : A),
      etaEq A x y -> etaEq A y z -> etaEq A x z
    | etaEq_eta : forall (A B : Set) (f : A -> B),
      etaEq (A -> B) f (fun x : A => f x).

Arguments etaEq [A] _ _.

Hint Constructors etaEq.

Instance etaEq_Equivalence (A : Set) : Equivalence (@etaEq A).
Proof. split; eauto. Defined.

Inductive ext : forall A : Set, A -> A -> Prop :=
    | ext_eq : forall (A : Set) (x y : A), x = y -> ext A x y
    | ext_trans : forall (A : Set) (x y z : A), ext A x y -> ext A y z -> ext A x z
    | ext_ext : forall (A B : Set) (f g : A -> B),
      (forall x : A, ext B (f x) (g x)) -> ext (A -> B) f g.

Arguments ext [A] _ _.

Hint Constructors ext.

Instance ext_Equivalence (A : Set) : Equivalence (@ext A).
Proof.
  split; red; eauto. induction 1; auto. eapply ext_trans; eauto.
Defined.

Theorem ext_Proper : forall (A B : Set) (f : A -> B),
    Proper (@ext A ==> @ext B) f.
Proof.
  repeat red; intros. induction H; subst.
    auto.
    eapply ext_trans; eauto.
    apply ext_ext in H.
Abort.

Inductive eta : forall A : Set, A -> A -> Prop :=
    | eta_eq : forall (A : Set) (x y : A), x = y -> eta A x y
    | eta_r : forall (A B : Set) (f : A -> B),
        eta (A -> B) f (fun x : A => f x)
    | eta_l : forall (A B : Set) (f : A -> B),
        eta (A -> B) (fun x : A => f x) f.

Arguments eta [A] _ _.

Hint Constructors eta.

Instance eta_Equivalence (A : Set) : Equivalence (@eta A).
Proof.
  split; red; intros.
    constructor. auto.
    destruct H; subst.
      auto.
      apply eta_l.
      apply eta_r.
    destruct H; subst; auto.
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
(* REMOVE THIS SOON *)    
| depExtEq_unext : forall (A : Type) (B C : A -> Type)
      (f : forall x : A, B x) (g : forall x : A, C x),
      depExtEq _ _ f g ->
      forall x y : A, depExtEq _ _ x y ->
      depExtEq _ _ (f x) (g y)
(* BA DUM TSSSS *)
    | depExtEq_unext' : forall (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type)
      (f : forall x : A1, B1 x) (g : forall x : A2, B2 x),
      depExtEq _ _ f g -> forall (x : A1) (y : A2), depExtEq _ _ x y ->
      depExtEq _ _ (f x) (g y).

Arguments depExtEq [A] [B] _ _.

Hint Constructors depExtEq.

Instance depExtEq_Equivalence (A : Set) : Equivalence (@depExtEq A A).
Proof.
  split; red; simpl; intros; eauto.
Defined.

Ltac solve_depExtEq := repeat 
match goal with
    | |- depExtEq (fun _ => _) (fun _ => _) => apply depExtEq_ext; intro
    | H : depExtEq ?f ?g |- depExtEq (?f _ _ _) (?g _ _ _) =>
      apply (depExtEq_unext' _ _ _ _ (f _ _) (g _ _))
    | H : depExtEq ?f ?g |- depExtEq (?f _ _) (?g _ _) =>
      apply (depExtEq_unext' _ _ _ _ (f _) (g _))
    | H : depExtEq ?f ?g |- depExtEq (?f _) (?g _) => 
      apply (depExtEq_unext' _ _ _ _ f g)
end; auto.

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
    : Prop := P x /\  (forall y : A, P y -> x == y).

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

(* TODO: possibly remove
Definition invertible {A B : Type} (S : Setoid B) (f : A -> B) : Type :=
    forall b : B, {a : A | f a == b}.*)

Hint Unfold injective surjective bijective injectiveS
    surjectiveS bijectiveS.

Ltac proper :=
match goal with
    | |- context [Proper] => unfold Proper, respectful; simpl; intros; proper
    | H : ?a == ?b |- _ => try rewrite H; clear H; proper
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
    (*| H : exists x, _ |- _ => destruct H
    | H : exists! x, _ |- _ => destruct H
    | H : exists!! x : _, _ |- _ => destruct H; unfold setoid_unique in **)
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
    | _ => my_simpl; eauto
end.

Instance Setoid_kernel {A B : Type} (f : A -> B) : Setoid A :=
    {| equiv := fun a a' : A => f a = f a' |}.
Proof. solve_equiv. Defined.

Instance Setoid_kernel_equiv {A B : Type} (S : Setoid B) (f : A -> B)
    : Setoid A := {| equiv := fun a a' : A => f a == f a' |}.
Proof. solve_equiv. Defined.