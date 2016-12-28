Require Export Coq.Classes.SetoidClass.
Require Export Coq.Logic.ProofIrrelevance.
Require Export JMeq.

Global Set Universe Polymorphism.

Class Cat : Type :=
{
    Ob : Type;
    Hom : Ob -> Ob -> Type;
    HomSetoid :> forall A B : Ob, Setoid (Hom A B);
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C;
    comp_Proper :> forall A B C : Ob,
        Proper (equiv ==> equiv ==> equiv) (@comp A B C);
    comp_assoc : forall (A B C D : Ob) (f : Hom A B) (g : Hom B C)
        (h : Hom C D), comp (comp f g) h == comp f (comp g h);
    id : forall A : Ob, Hom A A;
    id_left : forall (A B : Ob) (f : Hom A B), comp (id A) f == f;
    id_right : forall (A B : Ob) (f : Hom A B), comp f (id B) == f
}.

Arguments Ob _ : clear implicits.

Notation "f .> g" := (comp f g) (at level 50).

Hint Resolve comp_Proper comp_assoc id_left id_right.

(* Moved here so that tactics work *)
Definition setoid_unique {A : Type} {S : Setoid A} (P : A -> Prop) (x : A)
    : Prop := P x /\  (forall y : A, P y -> x == y).

Definition setoid_unique_t {A : Type} {S : Setoid A} (P : A -> Type) (x : A)
    : Type := P x * (forall y : A, P y -> x == y).

Notation "'exists' !! x : A , P" :=
    (ex (@setoid_unique A _ (fun x => P))) (at level 200, x ident).

Notation "{!  x : A | P  !}" :=
    (sig (@setoid_unique A _ (fun x => P))) (at level 200, x ident).

Notation "{!  x : A & P  !}" :=
    (sigT (@setoid_unique_t A _ (fun x => P))) (at level 200, x ident).

Ltac rw_id := match goal with
    | |- context [id _ .> _] => rewrite id_left
    | |- context [_ .> id _] => rewrite id_right
    | H : context [id _ .> _] |- _ => rewrite id_left in H
    | H : context [_ .> id _] |- _ => rewrite id_right in H
end.

Ltac rw_assoc := rewrite comp_assoc.
Ltac rw_assoc' := rewrite <- comp_assoc.

Ltac proper :=
match goal with
    | |- context [Proper] => unfold Proper, respectful; simpl; intros; proper
    | H : ?a == ?b |- _ => try rewrite H; clear H; proper
    | |- ?a == ?a => reflexivity
    | _ => idtac
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
    | H : exists x, _ |- _ => destruct H
    | H : exists! x, _ |- _ => destruct H
    | H : exists!! x : _, _ |- _ => destruct H; unfold setoid_unique in *
    | H : {_ | _} |- _ => destruct H
    | H : {_ : _ | _} |- _ => destruct H
    | H : {_ : _ & _} |- _ => destruct H
    | H : {! _ : _ | _ !} |- _ => destruct H
    | H : {! _ : _ & _ !} |- _ => destruct H
    | H : context [setoid_unique] |- _ => red in H
    | H : context [setoid_unique_t] |- _ => destruct H
    | |- context [setoid_unique] => split
    | |- context [setoid_unique_t] => split
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

Ltac cat_aux := repeat (my_simpl || intros || rw_id || rw_assoc ||
    reflexivity || subst; eauto (*10*)).
Ltac cat_aux' := repeat (my_simpl || intros || rw_id || rw_assoc' ||
    reflexivity || subst; eauto (*10*)).
Ltac cat := cat_aux || cat_aux'.

Instance Setoid_kernel {A B : Type} (f : A -> B) : Setoid A :=
    {| equiv := fun a a' : A => f a = f a' |}.
Proof. solve_equiv. Defined.

Instance Setoid_kernel_equiv {A B : Type} (S : Setoid B) (f : A -> B)
    : Setoid A := {| equiv := fun a a' : A => f a == f a' |}.
Proof. solve_equiv. Defined.

Instance Dual (C : Cat) : Cat :=
{|
    Ob := Ob C;
    Hom := fun A B : Ob C => Hom B A;
    HomSetoid := fun A B : Ob C => {| equiv := fun f g : Hom B A =>
        @equiv (Hom B A) (@HomSetoid C B A) f g |};
    comp := fun (X Y Z : Ob C) (f : @Hom C Y X) (g : @Hom C Z Y) => comp g f;
    id := @id C
|}.
Proof.
  (* Equivalence *) solve_equiv.
  (* Comp is proper *) proper.
  (* Category laws *) all: cat.
Defined.

Axiom dual_involution_axiom : forall (C : Cat), Dual (Dual C) = C.

Theorem duality_principle : forall (P : Cat -> Prop),
    (forall C : Cat, P C) -> (forall C : Cat, P (Dual C)).
Proof. trivial. Qed.

Definition End (C : Cat) {A B : Ob C} (f : Hom A B) : Prop := A = B.
Definition Mon (C : Cat) {A B : Ob C} (f : Hom A B) : Prop :=
    forall (X : Ob C) (g h : Hom X A), g .> f == h .> f -> g == h.
Definition Epi (C : Cat) {A B : Ob C} (f : Hom A B) : Prop :=
    forall (X : Ob C) (g h : Hom B X), f .> g == f .> h -> g == h.
Definition Bim (C : Cat) {A B : Ob C} (f : Hom A B) : Prop := Mon C f /\ Epi C f.
Definition Sec (C : Cat) {A B : Ob C} (f : Hom A B) : Type :=
    {g : Hom B A | f .> g == id A}.
Definition Ret (C : Cat) {A B : Ob C} (f : Hom A B) : Type :=
    {g : Hom B A | g .> f == id B}.
Definition Iso (C : Cat) {A B : Ob C} (f : Hom A B ) : Type :=
    {g : Hom B A | f .> g == id A /\ g .> f == id B}.
Definition Aut (C : Cat) {A : Ob C} (f : Hom A A) : Type := Iso C f.

Hint Unfold End Mon Epi Bim Sec Ret Iso Aut.

Theorem dual_mon_epi : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Mon C f <-> Epi (Dual C) f.
Proof.
  unfold Mon, Epi; split; intros.
    apply H. unfold comp, Dual in H0. assumption.
    apply H. unfold comp, Dual. assumption.
Restart.
  cat.
Qed.

Theorem dual_bim_self : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Bim C f <-> Bim (Dual C) f.
Proof.
  intros C A B f; unfold Bim. repeat rewrite (dual_mon_epi).
  repeat split; destruct H; assumption.
Restart.
  unfold Bim; cat.
Qed.

Theorem dual_sec_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Sec C f -> Ret (Dual C) f.
Proof. cat. Qed.

Theorem dual_ret_sec : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Ret C f -> Sec (Dual C) f.
Proof. cat. Qed.

Theorem dual_iso_self : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso C f -> Iso (Dual C) f.
Proof. unfold Iso; cat. Qed.

Theorem iso_inv_unique : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso C f -> {! g : Hom B A | f .> g == id A /\ g .> f == id B !}.
Proof.
  unfold Iso. destruct 1 as [g [inv1 inv2]].
  exists g. cat.
    assert (eq1 : y .> f .> g == g). rewrite H0. cat.
    assert (eq2 : y .> f .> g == y). rewrite comp_assoc, inv1. cat.
  rewrite <- eq1, eq2. reflexivity.
Qed.

Theorem iso_inv_unique_conv : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    {! g : Hom B A | f .> g == id A /\ g .> f == id B !} -> Iso C f.
Proof. unfold Iso. cat. Defined.

Definition isomorphic (C : Cat) (A B : Ob C) : Type :=
    {f : Hom A B & Iso C f}.

Definition uniquely_isomorphic (C : Cat) (A B : Ob C) : Type :=
    {! f : Hom A B & Iso C f !}.

Notation "A ~ B" := (isomorphic _ A B) (at level 50).
Notation "A ~~ B" := (uniquely_isomorphic _ A B) (at level 50).

Hint Unfold isomorphic uniquely_isomorphic setoid_unique.

Theorem dual_isomorphic_self : forall (C : Cat) (A B : Ob C),
    isomorphic C A B -> isomorphic (Dual C) B A.
Proof.
  unfold isomorphic; simpl.
  destruct 1 as [f [g [eq1 eq2]]]; exists f; red; cat.
Defined.

Theorem dual_isomorphic_self_conv : forall (C : Cat) (A B : Ob C),
    isomorphic (Dual C) B A -> isomorphic C A B.
Proof.
  unfold isomorphic; simpl.
  destruct 1 as [f [g [eq1 eq2]]]; exists f; red; cat.
Defined.

Theorem dual_unique_iso_self : forall (C : Cat) (A B : Ob C),
    uniquely_isomorphic C A B -> uniquely_isomorphic (Dual C) A B.
Proof.
  (* It works, but it's slow — I don't know why. *)
  unfold uniquely_isomorphic; simpl. destruct 1 as [f [f_iso H]].
  apply iso_inv_unique in f_iso. unfold Iso.
  destruct f_iso as [g [[eq1 eq2] unique]].
  exists g. cat. apply unique; rewrite (H x); cat.
Defined.

Theorem dual_unique_iso_self_conv : forall (C : Cat) (A B : Ob C),
    uniquely_isomorphic (Dual C) A B -> uniquely_isomorphic C A B.
Proof.
  unfold uniquely_isomorphic; simpl in *. destruct 1 as [f [f_iso H]].
  apply iso_inv_unique in f_iso. unfold Iso.
  destruct f_iso as [g [[eq1 eq2] unique]].
  exists g. cat. apply unique; rewrite (H x); cat.
  red. simpl. exists y. cat.
Qed.

Theorem unique_iso_is_iso : forall (C : Cat) (A B : Ob C),
    A ~~ B -> A ~ B.
Proof.
  unfold uniquely_isomorphic, isomorphic.
  destruct 1 as [f [H _]]. exists f; apply H.
Restart.
  unfold uniquely_isomorphic, isomorphic. cat.
Qed.

(* The identity is unique. *)
Theorem id_unique_left : forall (C : Cat) (A : Ob C) (idA : Hom A A),
    (forall (B : Ob C) (f : Hom A B), idA .> f == f) -> idA == id A.
Proof.
  intros. specialize (H A (id A)). cat.
Qed.

Theorem id_unique_right : forall (C : Cat) (B : Ob C) (idB : Hom B B),
    (forall (A : Ob C) (f : Hom A B), f .> idB == f) -> idB == id B.
Proof.
  intros. specialize (H B (id B)). cat.
Qed.

(* Relations between different types of morphisms. *)
Theorem sec_is_mon : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Sec C f -> Mon C f.
Proof.
  destruct 1 as [g H]. red. intros X h1 h2 eq.
  assert (eq2 : (h1 .> f) .> g == (h2 .> f) .> g).
    rewrite eq; reflexivity.
  do 2 rewrite comp_assoc in eq2. rewrite H in eq2. cat.
Qed.

Theorem ret_is_epi : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Ret C f -> Epi C f.
Proof.
  destruct 1 as [g H]. red. intros X h1 h2 eq.
  assert (eq2 : g .> (f .> h1) == g .> (f .> h2)).
    rewrite eq; reflexivity.
  do 2 rewrite <- comp_assoc in eq2. rewrite H in eq2. cat.
Qed.

Theorem iso_is_sec : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso C f -> Sec C f.
Proof.
  unfold Iso, Sec; cat.
Qed.

Theorem iso_is_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Iso C f -> Ret C f.
Proof.
  unfold Iso, Ret; cat.
Qed.

(* Kinds of ordinary functions. The suffix "S" at the end of some
   of these stands for "Setoid", "T" will stand for "Type". *)
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

Definition invertible {A B : Type} (S : Setoid B) (f : A -> B) : Type :=
    forall b : B, {a : A | f a == b}.

(* Characterizations. *)
Theorem mon_char : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Mon C f -> forall X : Ob C, injectiveS (fun g : Hom X A => g .> f).
Proof.
  unfold Mon, injectiveS; intros. apply H. assumption.
Defined.

Theorem mon_char_conv : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    (forall X : Ob C, injectiveS (fun g : Hom X A => g .> f)) -> Mon C f.
Proof.
  unfold Mon, injectiveS; intros. apply H. assumption.
Defined. 

Theorem epi_char : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Epi C f -> forall X : Ob C, injectiveS (fun g : Hom B X => f .> g).
Proof. cat. red. cat. Qed.

Theorem epi_char_conv : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    (forall X : Ob C, injectiveS (fun g : Hom B X => f .> g)) -> Epi C f.
Proof. cat. Defined.

Theorem iso_is_sec_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Sec C f -> Ret C f -> Iso C f.
Proof.
  destruct 1 as [g f_sec], 1 as [h f_ret].
  assert (eq1 : h .> f .> g == h). rewrite comp_assoc. rewrite f_sec. cat.
  assert (eq2 : h .> f .> g == g). rewrite f_ret; cat.
  assert (eq : g == h). rewrite <- eq1, eq2. reflexivity.
  exists g. split. assumption. rewrite eq. assumption.
Defined.

Theorem iso_is_sec_epi : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Sec C f -> Epi C f -> Iso C f.
Proof.
  destruct 1 as [g g_sec]; unfold Epi, Iso; intros.
  exists g. split. assumption.
  apply H. rewrite <- comp_assoc. rewrite g_sec. cat.
Defined.

Theorem iso_is_mon_ret : forall (C : Cat) (A B : Ob C) (f : Hom A B),
    Mon C f -> Ret C f -> Iso C f.
Proof.
  unfold Mon, Iso; destruct 2 as [g g_ret]; intros.
  exists g. split; try assumption.
  apply H. rewrite comp_assoc. rewrite g_ret. cat.
Defined.

(* Composition theorems. *)
Theorem mon_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Mon C f -> Mon C g -> Mon C (f .> g).
Proof.
  unfold Mon. cat. apply H, H0. cat.
Defined.

Theorem epi_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Epi C f -> Epi C g -> Epi C (f .> g).
Proof.
  unfold Epi. cat. apply H0, H. cat.
Defined.

Hint Resolve mon_comp epi_comp.

Theorem bim_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Bim C f -> Bim C g -> Bim C (f .> g).
Proof.
  unfold Bim; cat.
Defined.

Theorem sec_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Sec C f -> Sec C g -> Sec C (f .> g).
Proof.
  destruct 1 as [h1 eq1], 1 as [h2 eq2]. red. exists (h2 .> h1).
  rewrite comp_assoc, <- (comp_assoc _ _ _ _ g h2). rewrite eq2. cat.
Defined.

Theorem ret_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Ret C f -> Ret C g -> Ret C (f .> g).
Proof.
  destruct 1 as [h1 eq1], 1 as [h2 eq2]. exists (h2 .> h1).
  rewrite comp_assoc, <- (comp_assoc _ _ _ _ h1 f). rewrite eq1. cat.
Defined.

Hint Resolve iso_is_sec_ret iso_is_sec iso_is_ret sec_comp ret_comp.

Theorem iso_comp : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Iso C f -> Iso C g -> Iso C (f .> g).
Proof.
  intros. apply iso_is_sec_ret; cat.
Defined.

Hint Resolve iso_comp.

Theorem aut_comp : forall (C : Cat) (X : Ob C)
    (f : Hom X X) (g : Hom X X), Aut C f -> Aut C g -> Aut C (f .> g).
Proof. cat. Defined.

(* Composition properties. *)
Theorem mon_prop : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Mon C (f .> g) -> Mon C f.
Proof.
  unfold Mon; intros. apply H. repeat rewrite <- comp_assoc.
  rewrite H0. reflexivity.
Defined.

Theorem epi_prop : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Epi C (f .> g) -> Epi C g.
Proof.
  unfold Epi; intros. apply H.
  repeat rewrite comp_assoc. rewrite H0. reflexivity.
Defined.

Theorem ret_prop : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Ret C (f .> g) -> Ret C g.
Proof.
  unfold Ret. destruct 1 as [h eq]. exists (h .> f). cat.
Defined.

Theorem sec_prop : forall (C : Cat) (X Y Z : Ob C)
    (f : Hom X Y) (g : Hom Y Z), Sec C (f .> g) -> Sec C f.
Proof.
  unfold Sec. destruct 1 as [h eq]. exists (g .> h). rewrite <- eq; cat.
Qed.

Theorem id_is_aut : forall (C : Cat) (X : Ob C), Aut C (id X).
Proof. unfold Aut, Iso; intros; exists (id X); cat. Defined.

(*Instance isomorphic_equiv (C : Cat) : Equivalence (isomorphic C).
Proof.
  split; do 2 red; intros.
  (* Reflexivity *) exists (id x). apply id_is_aut.
  (* Symmetry *) destruct H as [f [g [eq1 eq2]]]. unfold Iso.
    exists g, f; auto.
  (* Transitivity *) destruct H as [f f_iso], H0 as [g g_iso].
    exists (f .> g). apply iso_comp; assumption.
Defined.*)