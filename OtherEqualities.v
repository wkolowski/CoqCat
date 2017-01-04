Require Export Base.

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

(* TODO: this is all shit *)
Require Import Coq.Logic.Eqdep.
Print eq_dep.
Inductive depExtEq :
  forall (A : Type) (B : A -> Type) (a : A) (b : B a), Prop :=
    | depExtEq_refl : forall (A : Type) (x : A),
        depExtEq A A x x
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
        depExtEq _ _ f g -> forall (x : A1) (y : A2), depExtEq _ _ x y ->
        depExtEq _ _ (f x) (g y).

Arguments depExtEq [A] [B] _ _.

Hint Constructors depExtEq.

Instance depExtEq_Equivalence (A : Set) : Equivalence (@depExtEq A A).
Proof.
  split; red; simpl; intros; eauto.
Defined.

Theorem depExtEq_Proper : forall (A B : Type) (f : A -> B),
    Proper (@depExtEq A A ==> @depExtEq B B) f.
Proof.
  repeat red. intros. generalize dependent f.
  induction H; intros.
    auto.
    apply depExtEq_sym. specialize (f x). specialize (IHdepExtEq f). apply IHdepExtEq. auto.