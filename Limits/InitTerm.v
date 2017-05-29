Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.

Definition initial {C : Cat} (I : Ob C) : Prop :=
    forall (X : Ob C), exists!! f : Hom I X, True.

Definition terminal {C : Cat} (T : Ob C) : Prop :=
    forall (X : Ob C), exists!! f : Hom X T, True.

Definition zero_object {C : Cat} (Z : Ob C) : Prop :=
    initial Z /\ terminal Z.

Definition initial_skolem {C : Cat} (I : Ob C)
  (create : forall X : Ob C, Hom I X) : Prop :=
  forall X : Ob C,
    setoid_unique (fun _ => True) (create X).

Class has_init (C : Cat) : Type :=
{
    init : Ob C;
    create : forall X : Ob C, Hom init X;
    is_initial : forall (X : Ob C) (f : Hom init X), f == create X
}.

Arguments init _ [has_init].
Arguments create [C] [has_init] _.

Class has_term (C : Cat) : Type :=
{
    term : Ob C;
    delete : forall X : Ob C, Hom X term;
    is_terminal : forall (X : Ob C) (f : Hom X term), f == delete X
}.

Arguments term _ [has_term].
Arguments delete [C] [has_term] _.

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
  pose (f := delete X). pose (g := create Y).
  rewrite initial_is_terminal in g. exact (f .> g).
Defined.

Hint Unfold initial terminal zero_object.
Hint Resolve is_initial is_terminal initial_is_terminal unique_iso_is_iso.

Ltac init := intros; repeat
match goal with
    | (*ht : has_init ?C*) |- context [?f] =>
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

Theorem dual_initial_terminal : forall (C : Cat) (A : Ob C),
    @initial C A <-> @terminal (Dual C) A.
Proof. split; auto. Qed.

Theorem dual_zero_self : forall (C : Cat) (A : Ob C),
    @zero_object C A <-> @zero_object (Dual C) A.
Proof.
  unfold zero_object; repeat split; intros;
  destruct H; assumption.
Qed.

Theorem initial_uiso : forall (C : Cat) (A B : Ob C),
    initial A -> initial B -> A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic, initial; intros.
  destruct (H B) as [f [_ Hf]],
           (H0 A) as [g [_ Hg]],
           (H A) as [idA [_ HA]],
           (H0 B) as [idB [_ HB]].
  exists f; red. split; auto. exists g; split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Qed.

Theorem initial_skolem_uiso :
  forall (C : Cat) (A B : Ob C)
  (create : forall X : Ob C, Hom A X)
  (create' : forall X : Ob C, Hom B X),
    initial_skolem A create -> initial_skolem B create' ->
    A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic, initial; intros.
  red in H. red in H0.
  destruct (H B) as [_ Hf],
           (H0 A) as [_ Hg],
           (H A) as [_ HA],
           (H0 B) as [_ HB].
  exists (create0 B); red. split; auto. exists (create' A); split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Qed.

Hint Resolve initial_uiso.

Theorem initial_iso : forall (C : Cat) (A B : Ob C),
    initial A -> initial B -> A ~ B.
Proof. auto. Defined.

Theorem terminal_uiso : forall (C : Cat) (A B : Ob C),
    terminal A -> terminal B -> A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic, terminal; intros.
  destruct (H B) as [f [_ Hf]], (H0 A) as [g [_ Hg]], (H A) as [idA [_ HA]],
    (H0 B) as [idB [_ HB]].
  exists g; red. split; auto. exists f; split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Restart.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite <- dual_initial_terminal in *.
  rewrite dual_unique_iso_self. cat.
Qed.

Hint Resolve terminal_uiso.

Theorem terminal_iso : forall (C : Cat) (A B : Ob C),
    terminal A -> terminal B -> A ~ B.
Proof. auto. Qed.

Theorem zero_unique_iso : forall (C : Cat) (A B : Ob C),
    zero_object A -> zero_object B -> A ~~ B.
Proof. unfold zero_object; cat. Qed.

Hint Resolve zero_unique_iso.

Theorem zero_iso : forall (C : Cat) (A B : Ob C),
    zero_object A -> zero_object B -> A ~ B.
Proof. auto. Qed.

Theorem iso_to_init_is_init : forall (C : Cat) (I X : Ob C),
    initial I -> I ~ X -> initial X.
Proof.
  intros. destruct H0 as [f [g [eq1 eq2]]].
  unfold initial in *. intro X'.
  destruct (H X') as [create [_ Hcreate]].
  exists (g .> create). split; intros; auto.
    specialize (Hcreate (f .> y) H0). rewrite Hcreate.
      rewrite <- comp_assoc. rewrite eq2. rewrite id_left. reflexivity.
Defined.

Theorem iso_to_term_is_term : forall (C : Cat) (T X : Ob C),
    terminal T -> T ~ X -> terminal X.
Proof.
  intros. destruct H0 as [f [g [eq1 eq2]]].
  unfold terminal in *. intro X'.
  destruct (H X') as [del [_ Hdel]].
  exists (del .> f). split; intros; auto.
    specialize (Hdel (y .> g) H0). rewrite Hdel.
      rewrite comp_assoc. rewrite eq2. rewrite id_right. reflexivity.
Qed.

Theorem mor_to_init_is_ret : forall (C : Cat) (I X : Ob C) (f : Hom X I),
    initial I -> Ret f.
Proof.
  unfold initial, Ret; intros.
  destruct (H X) as (g, [_ eq1]), (H I) as (idI, [_ eq2]). exists g.
  rewrite <- (eq2 (g .> f)); try rewrite <- (eq2 (id I)); reflexivity.
Qed.

Theorem mor_from_term_is_sec : forall (C : Cat) (T X : Ob C) (f : Hom T X),
    terminal T -> Sec f.
Proof.
  unfold terminal, Sec; intros.
  destruct (H X) as (g, [_ eq1]), (H T) as (idT, [_ eq2]). exists g.
  rewrite <- (eq2 (f .> g)); try rewrite <- (eq2 (id T)); reflexivity.
Qed.

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

Instance Dual_has_zero (C : Cat) (hz : has_zero C) : has_zero (Dual C) :=
{
    zero_is_initial := Dual_has_init C hz;
    zero_is_terminal := Dual_has_term C hz
}.
Proof. cat. Defined.