Require Import Cat.Base.

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

Instance ext_Proper : forall (A B : Set) (f : A -> B),
    Proper (@ext A ==> @ext B) f.
Proof.
  repeat red; intros. induction H; subst.
    auto.
    eapply ext_trans; eauto.
    apply ext_ext in H.
Abort.

(* TODO: put equalities here *)

(*Inductive JMequiv_ext : forall (A : Type) (_ : Setoid A) (B : Type),
    A -> B -> Prop :=
    | JMequiv_equiv : forall (A B : Type), Setoid A ->
        forall x y : A, x == y -> JMequiv_ext x y.
    | JMequiv_ext : forall *)