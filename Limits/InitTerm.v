Require Export Cat.

Set Implicit Arguments.

Definition initial {C : Cat} (I : Ob C)
  (create : forall X : Ob C, Hom I X) : Prop :=
    forall X : Ob C, setoid_unique (fun _ => True) (create X).

Definition terminal {C : Cat} (T : Ob C)
  (delete : forall X : Ob C, Hom X T) : Prop :=
    forall X : Ob C, setoid_unique (fun _ => True) (delete X).

Definition zero {C : Cat} (Z : Ob C)
  (create : forall X : Ob C, Hom Z X)
  (delete : forall X : Ob C, Hom X Z) : Prop :=
    initial Z create /\ terminal Z delete.

Class has_init (C : Cat) : Type :=
{
    init : Ob C;
    create : forall X : Ob C, Hom init X;
    is_initial : forall (X : Ob C) (f : Hom init X), f == create X
}.

Arguments init _ {has_init}.
Arguments create {C has_init}_.

Class has_term (C : Cat) : Type :=
{
    term : Ob C;
    delete : forall X : Ob C, Hom X term;
    is_terminal : forall (X : Ob C) (f : Hom X term), f == delete X
}.

Arguments term _ {has_term}.
Arguments delete {C has_term} _.

Class has_zero (C : Cat) : Type :=
{
    zero_is_initial :> has_init C;
    zero_is_terminal :> has_term C;
    initial_is_terminal : init C = term C
}.

Coercion zero_is_initial : has_zero >-> has_init.
Coercion zero_is_terminal : has_zero >-> has_term.

Definition zero_ob (C : Cat) {hz : has_zero C} : Ob C := init C.
Definition zero_mor (C : Cat) {hz : has_zero C}
    (X Y : Ob C) : Hom X Y.
Proof.
  pose (f := delete X). pose (g := create Y).
  rewrite initial_is_terminal in g. exact (f .> g).
Defined.

Hint Resolve is_initial is_terminal initial_is_terminal unique_iso_is_iso.

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

Theorem dual_initial_terminal :
  forall (C : Cat) (X : Ob C)
  (create : forall X' : Ob C, Hom X X'),
    @initial C X create <-> @terminal (Dual C) X create.
Proof. cat. Qed.

Theorem dual_zero_self :
  forall (C : Cat) (X : Ob C)
  (create : forall X' : Ob C, Hom X X')
  (delete : forall X' : Ob C, Hom X' X),
    @zero C X create delete <-> @zero (Dual C) X delete create.
Proof.
  unfold zero; cat.
Qed.

Theorem initial_uiso :
  forall (C : Cat) (A B : Ob C)
  (create : forall X : Ob C, Hom A X)
  (create' : forall X : Ob C, Hom B X),
    initial A create -> initial B create' ->
      A ~~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic; intros.
  red in H. red in H0.
  destruct (H B) as [_ Hf],
           (H0 A) as [_ Hg],
           (H A) as [_ HA],
           (H0 B) as [_ HB].
  exists (create0 B); red. split; auto. exists (create' A); split.
    rewrite <- (HA (id A)); try symmetry; auto.
    rewrite <- (HB (id B)); try symmetry; auto.
Qed.

Theorem initial_iso :
  forall (C : Cat) (A B : Ob C)
  (create : forall X : Ob C, Hom A X)
  (create' : forall X : Ob C, Hom B X),
    initial A create -> initial B create' ->
      A ~ B.
Proof.
  intros. destruct (initial_uiso H H0). cat.
Qed.

Theorem initial_create_equiv :
  forall (C : Cat) (I : Ob C)
  (create : forall X : Ob C, Hom I X)
  (create' : forall X : Ob C, Hom I X),
    initial I create ->
    initial I create' ->
      forall X : Ob C, create X == create' X.
Proof.
  intros. edestruct H. apply H2. trivial.
Qed.

Theorem terminal_uiso :
  forall (C : Cat) (A B : Ob C)
  (delete : forall X : Ob C, Hom X A)
  (delete' : forall X : Ob C, Hom X B),
    terminal A delete -> terminal B delete' ->
      A ~~ B.
Proof.
  intro C. rewrite <- (dual_involution_axiom C); simpl; intros.
  rewrite <- dual_initial_terminal in *.
  rewrite dual_unique_iso_self.
  eapply initial_uiso; cat.
Qed.

Theorem terminal_iso :
  forall (C : Cat) (A B : Ob C)
  (delete : forall X : Ob C, Hom X A)
  (delete' : forall X : Ob C, Hom X B),
    terminal A delete -> terminal B delete' ->
      A ~ B.
Proof.
  intros. destruct (terminal_uiso H H0). cat.
Qed.

Theorem terminal_delete_equiv :
  forall (C : Cat) (T : Ob C)
  (delete : forall X : Ob C, Hom X T)
  (delete' : forall X : Ob C, Hom X T),
    terminal T delete ->
    terminal T delete' ->
      forall X : Ob C, delete X == delete' X.
Proof.
  intros. edestruct H. apply H2. trivial.
Qed.

Theorem iso_to_init_is_init :
  forall (C : Cat) (I X : Ob C)
  (create : forall I' : Ob C, Hom I I'),
    initial I create -> forall f : Hom X I, Iso f ->
      initial X (fun X' : Ob C => f .> create X').
Proof.
  repeat split; intros. iso.
  edestruct H. rewrite (H1 (f_inv .> y)). cat.
    assocl. rewrite f_inv_eq1. cat.
    trivial.
Defined.

Theorem iso_to_term_is_term : 
  forall (C : Cat) (X T : Ob C)
  (delete : forall T' : Ob C, Hom T' T),
    terminal T delete -> forall f : Hom T X, Iso f ->
      terminal X (fun X' : Ob C => delete X' .> f).
Proof.
  repeat split; intros. iso.
  edestruct H. rewrite (H1 (y .> f_inv)).
    assocr. rewrite f_inv_eq2. cat.
    trivial.
Defined.

Theorem mor_to_init_is_ret :
  forall (C : Cat) (I X : Ob C) (f : Hom X I)
  (create : forall I' : Ob C, Hom I I'),
    initial I create -> Ret f.
Proof.
  intros. red. exists (create0 X).
  edestruct H. rewrite <- H1; cat.
Qed.

Theorem mor_from_term_is_sec :
  forall (C : Cat) (T X : Ob C) (f : Hom T X)
  (delete : forall T' : Ob C, Hom T' T),
    terminal T delete -> Sec f.
Proof.
  intros. red. exists (delete0 X).
  edestruct H. rewrite <- H1; cat.
Qed.

#[refine]
Instance Dual_has_term (C : Cat) (hi : has_init C) : has_term (Dual C) :=
{
    term := init C;
    delete := @create C hi
}.
Proof. cat. Defined.

#[refine]
Instance Dual_has_init (C : Cat) (ht : has_term C) : has_init (Dual C) :=
{
    init := term C;
    create := @delete C ht
}.
Proof. cat. Defined.

#[refine]
Instance Dual_has_zero (C : Cat) (hz : has_zero C) : has_zero (Dual C) :=
{
    zero_is_initial := Dual_has_init hz;
    zero_is_terminal := Dual_has_term hz
}.
Proof. cat. Defined.

(*
Theorem init_Hom :
  forall (C : Cat) (I : Ob C) (create : forall X : Ob C, Hom I X) (X : Ob C),
    initial I create <-> Hom I X ~ CoqSetoid_term.
Proof.
Abort.
*)