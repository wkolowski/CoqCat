Require Export Cat.

Definition initial (C : Cat) (I : Ob C) : Type :=
    forall (X : Ob C), {! f : Hom I X | True !}.

Definition terminal (C : Cat) (T : Ob C) : Type :=
    forall (X : Ob C), {! f : Hom X T | True !}.

Definition zero_object (C : Cat) (Z : Ob C) : Type :=
    initial C Z * terminal C Z.

Theorem dual_initial_terminal : forall (C : Cat) (A : Ob C),
    initial C A -> terminal (Dual C) A.
Proof. auto. Defined.

Theorem dual_terminal_initial : forall (C : Cat) (A : Ob C),
    terminal C A -> initial (Dual C) A.
Proof. auto. Defined.

Theorem dual_zero_self : forall (C : Cat) (A : Ob C),
    zero_object C A -> zero_object (Dual C) A.
Proof.
  unfold zero_object. destruct 1. cat.
Defined.

Class has_init (C : Cat) : Type :=
{
    init : Ob C;
    create : forall X : Ob C, Hom init X;
    is_initial : forall (X : Ob C) (f : Hom init X), f == create X
}.

Arguments init _ [has_init].
Arguments create _ [has_init] _.

Class has_term (C : Cat) : Type :=
{
    term : Ob C;
    delete : forall X : Ob C, Hom X term;
    is_terminal : forall (X : Ob C) (f : Hom X term), f == delete X
}.

Arguments term _ [has_term].
Arguments delete _ [has_term] _.

Class has_zero (C : Cat) : Type :=
{
    zero_is_initial :> has_init C;
    zero_is_terminal :> has_term C;
    initial_is_terminal : init C = term C
}.

Coercion zero_is_initial : has_zero >-> has_init.
Coercion zero_is_terminal : has_zero >-> has_term.

Definition zero_ob (C : Cat) {has_zero0 : has_zero C} : Ob C := init C.
Definition zero_mor (C : Cat) {has_zero0 : has_zero C}
    (X Y : Ob C) : Hom X Y.
Proof.
  pose (f := delete C X). pose (g := create C Y).
  rewrite initial_is_terminal in g. exact (f .> g).
Defined.

Hint Unfold initial terminal zero_object.
Hint Resolve is_initial is_terminal initial_is_terminal unique_iso_is_iso.

Theorem initial_uiso : forall (C : Cat) (A B : Ob C),
    initial C A -> initial C B -> A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic, initial; intros C A B H H0.
  destruct (H B) as [f [_ Hf]], (H0 A) as [g [_ Hg]], (H A) as [idA [_ HA]],
    (H0 B) as [idB [_ HB]].
  exists f; red. split; auto. exists g; split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Defined.

Hint Resolve initial_uiso.

Theorem initial_iso : forall (C : Cat) (A B : Ob C),
    initial C A -> initial C B -> A ~ B.
Proof. auto. Defined.

Theorem terminal_uiso : forall (C : Cat) (A B : Ob C),
    terminal C A -> terminal C B -> A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic, terminal; intros C A B H H0.
  destruct (H B) as [f [_ Hf]], (H0 A) as [g [_ Hg]], (H A) as [idA [_ HA]],
    (H0 B) as [idB [_ HB]].
  exists g; red. split; auto. exists f; split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Restart.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  apply dual_terminal_initial in X.
  apply dual_terminal_initial in X0.
  apply dual_unique_iso_self. cat.
Defined.

Hint Resolve terminal_uiso.

Theorem terminal_iso : forall (C : Cat) (A B : Ob C),
    terminal C A -> terminal C B -> A ~ B.
Proof. auto. Qed.

Theorem zero_unique_iso : forall (C : Cat) (A B : Ob C),
    zero_object C A -> zero_object C B -> A ~~ B.
Proof. unfold zero_object. destruct 1, 1. auto. Defined.

Hint Resolve zero_unique_iso.

Theorem zero_iso : forall (C : Cat) (A B : Ob C),
    zero_object C A -> zero_object C B -> A ~ B.
Proof. destruct 1, 1. auto. Defined.

Theorem mor_to_init_is_ret : forall (C : Cat) (I X : Ob C) (f : Hom X I),
    initial C I -> Ret C f.
Proof.
  unfold initial, Ret; intros C I X f H.
  destruct (H X) as (g, [_ eq1]), (H I) as (idI, [_ eq2]). exists g.
  rewrite <- (eq2 (g .> f)); try rewrite <- (eq2 (id I)); reflexivity.
Defined.

Theorem mor_from_term_is_sec : forall (C : Cat) (T X : Ob C) (f : Hom T X),
    terminal C T -> Sec C f.
Proof.
  unfold terminal, Sec; intros C T X f H.
  destruct (H X) as (g, [_ eq1]), (H T) as (idT, [_ eq2]). exists g.
  rewrite <- (eq2 (f .> g)); try rewrite <- (eq2 (id T)); reflexivity.
Defined.

Instance Dual_has_term (C : Cat) (hi : has_init C) : has_term (Dual C) :=
{
    term := init C;
    delete := @create C hi
}.
Proof. cat. Defined.

Instance Dual_has_init (C : Cat) (ht : has_term C) : has_init (Dual C) :=
{
    init := term C;
    create := @delete C ht
}.
Proof. cat. Defined.
Print has_zero.
Instance Dual_has_zero (C : Cat) (hz : has_zero C) : has_zero (Dual C) :=
{
    zero_is_initial := Dual_has_init C (@zero_is_terminal C hz);
    zero_is_terminal := Dual_has_term C (@zero_is_initial C hz)
}.
Proof. cat. Defined.