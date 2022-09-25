Require Export ProofIrrelevance FunctionalExtensionality IndefiniteDescription JMeq.
Require Export Setoid Classes.SetoidClass.
Require Export Equality.
Require Export Bool Arith Lia.

Require Export List.
Export ListNotations.

#[global] Set Universe Polymorphism.

(** * Equality *)

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
match p with
| eq_refl => u
end.

Lemma transport_transport :
  forall {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x),
    transport P q (transport P p u) = transport P (eq_trans p q) u.
Proof.
  now intros A P x y z [] [] u; cbn.
Defined.

Lemma unit_eq_intro :
  forall x y : unit, x = y.
Proof.
  now intros [] [].
Defined.

Lemma prod_eq_intro :
  forall {A B : Type} (x y : A * B),
    fst x = fst y -> snd x = snd y -> x = y.
Proof.
  now intros A B [] []; cbn; intros [] [].
Defined.

(** * Setoids *)

(** Uniqueness up to a custom equivalence relation, using setoids. *)

Definition setoid_unique {A : Type} {S : Setoid A} (P : A -> Prop) (x : A) : Prop :=
  P x /\ (forall y : A, P y -> x == y).

Set Warnings "-deprecated-ident-entry".
Notation "'exists' !! x : A , P" :=
  (ex (@setoid_unique A _ (fun x => P))) (at level 200, x ident).
Set Warnings "+deprecated-ident-entry".

#[global] Hint Unfold setoid_unique : core.

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
| x : True |- _ => clear x
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

(** Proving equality of setoids *)

Lemma setoid_split :
  forall A A' equiv equiv' setoid_equiv setoid_equiv',
    A = A' -> JMeq equiv equiv' ->
      JMeq (@Build_Setoid A equiv setoid_equiv) (@Build_Setoid A' equiv' setoid_equiv').
Proof.
  now intros; subst; replace setoid_equiv with setoid_equiv' by apply proof_irrelevance.
Qed.

(** Some setoid instances. *)

#[refine]
#[export]
Instance Setoid_forall
  {A : Type} {B : A -> Type} (H : forall x : A, Setoid (B x))
  : Setoid (forall x : A, B x) :=
{
  equiv := fun f g => forall x : A, f x == g x;
}.
Proof. now solve_equiv. Defined.

Definition Setoid_kernel {A B : Type} (f : A -> B) : Setoid A.
Proof.
  split with (fun a1 a2 : A => f a1 = f a2).
  now solve_equiv.
Defined.

Definition Setoid_kernel_equiv {A B : Type} (S : Setoid B) (f : A -> B) : Setoid A.
Proof.
  split with (fun a1 a2 : A => @equiv _ S (f a1) (f a2)).
  now solve_equiv.
Defined.

(** Sum-product hybrid. Useful for a few categories that behave like [Rel]. *)

Inductive sumprod (X Y : Set) : Set :=
| inl'  : X -> sumprod X Y
| inr'  : Y -> sumprod X Y
| pair' : X -> Y -> sumprod X Y.

Arguments inl'  [X Y] _.
Arguments inr'  [X Y] _.
Arguments pair' [X Y] _ _.

#[global] Hint Constructors sumprod : core.

(** Non-empty lists *)

Inductive nel (A : Type) : Type :=
| singl    : A -> nel A
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
  now induction x as [h | h t]; cbn; intros; rewrite ?IHt.
Qed.

Fixpoint nel_map {A B : Type} (f : A -> B) (l : nel A) : nel B :=
match l with
| singl x => singl (f x)
| h ::: t => f h ::: nel_map f t
end.

Fixpoint equiv_nel {X : Type} `{Setoid X} (l1 l2 : nel X) : Prop :=
match l1, l2 with
| singl h, singl h' => h == h'
| h ::: t, h' ::: t' => h == h' /\ equiv_nel t t'
| _, _ => False
end.

Lemma equiv_nel_refl :
  forall {X : Type} `{Setoid X} (l : nel X),
    equiv_nel l l.
Proof.
  now induction l as [| h t]; cbn; try rewrite IHt; solve_equiv.
Qed.

Lemma equiv_nel_sym :
  forall {X : Type} `{Setoid X} (l1 l2 : nel X),
    equiv_nel l1 l2 -> equiv_nel l2 l1.
Proof.
  now induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; solve_equiv.
Qed.

Lemma equiv_nel_trans :
  forall {X : Type} `{Setoid X} (l1 l2 l3 : nel X),
    equiv_nel l1 l2 -> equiv_nel l2 l3 -> equiv_nel l1 l3.
Proof.
  now induction l1 as [| h1 t1]; destruct l2, l3; solve_equiv.
Qed.

#[global] Hint Resolve equiv_nel_refl equiv_nel_sym equiv_nel_trans : core.

(*
Fixpoint fp_equiv {X Y : Type} `{Setoid X} `{Setoid Y} (l1 l2 : nel (X + Y)) : Prop :=
match l1, l2 with
| singl (inl x), singl (inl x') => x == x'
| singl (inr y), singl (inr y') => y == y'
| cons_nel (inl h1) t1, cons_nel (inl h2) t2 => h1 == h2 /\ fp_equiv t1 t2
| cons_nel (inr h1) t1, cons_nel (inr h2) t2 => h1 == h2 /\ fp_equiv t1 t2
| _, _ => False
end.

Ltac fp_equiv := intros; repeat
match goal with
| x : _ + _ |- _ => destruct x; cbn in *
| H : _ /\ _ |- _ => destruct H
| |- _ /\ _ => split
| |- ?x == ?x => reflexivity
| H : ?P |- ?P => assumption
| H : ?x == ?y |- ?y == ?x => symmetry; assumption
| |- _ == _ => solve_equiv
| H : False |- _ => inversion H
| _ => eauto
end.

Lemma fp_equiv_refl :
  forall {X Y : Type} `{Setoid X} `{Setoid Y} (l : nel (X + Y)),
    fp_equiv l l.
Proof.
  now induction l as [| h t]; fp_equiv.
Qed.

Lemma fp_equiv_sym :
  forall {X Y : Type} `{Setoid X} `{Setoid Y} (l1 l2 : nel (X + Y)),
    fp_equiv l1 l2 -> fp_equiv l2 l1.
Proof.
  now induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; fp_equiv.
Qed.

Lemma fp_equiv_trans :
  forall {X Y : Type} `{Setoid X} `{Setoid Y} (l1 l2 l3 : nel (X + Y)),
    fp_equiv l1 l2 -> fp_equiv l2 l3 -> fp_equiv l1 l3.
Proof.
  now induction l1 as [| h1 t1]; destruct l2, l3; fp_equiv.
Qed.

#[global] Hint Resolve fp_equiv_refl fp_equiv_sym fp_equiv_trans : core.
*)

Fixpoint nel2list {A : Type} (l : nel A) : list A :=
match l with
| singl h => [h]
| h ::: t => h :: nel2list t
end.

Lemma nel2list_app :
  forall {A : Type} (l1 l2 : nel A),
    nel2list (nel_app l1 l2) = nel2list l1 ++ nel2list l2.
Proof.
  now induction l1 as [h | h t]; cbn; intros; rewrite ?IHt.
Qed.