Require Import NPeano.
Require Import Omega.
Require Import ProofIrrelevance.

Require Export CatInstances.

Class Pros {A : Type} : Type :=
{
    leq : A -> A -> Prop;
    leq_refl : forall a : A, leq a a;
    leq_trans : forall a b c : A, leq a b -> leq b c -> leq a c
}.

Notation "a ≤ b" := (leq a b) (at level 50).

Definition Pros_Sort `(_ : Pros) := A.
Coercion Pros_Sort : Pros >-> Sortclass.

Class HomPros `(A : Pros) `(B : Pros) : Type :=
{
    f_ : A -> B;
    homo_pros : forall a a' : A, a ≤ a' -> f_ a ≤ f_ a'
}.

Definition HomPros_Fun `(_ : HomPros) := f_.
Coercion HomPros_Fun : HomPros >-> Funclass.

Class Pros' : Type :=
{
    carrier_ : Type;
    pros_ : @Pros carrier_
}.

Definition Pros'_Pros `(_ : Pros') := pros_.
Coercion Pros'_Pros : Pros' >-> Pros.

Instance HomPros' : @CatHom Pros'.
split. intros. exact (HomPros A B).
Defined.

Instance CompPros : @CatComp Pros' HomPros'.
split. intros A B C f g. unfold Hom, HomPros' in *.
split with (fun n => g (f n)).
destruct f, g. intros. apply homo_pros1, homo_pros0. assumption.
Defined.

Instance IdPros : @CatId Pros' HomPros'.
split. intro. split with (fun a => a). trivial.
Defined.

Instance CatPros : @Cat Pros' HomPros' CompPros IdPros.
split; intros; destruct f; simpl; f_equal; apply proof_irrelevance.
(*[destruct f | destruct f | destruct f];
simpl; f_equal. apply proof_irrelevance.*)
Defined.

Instance NatLe : @Pros nat.
split with le; intros; omega.
Defined.

Instance addOne : HomPros NatLe NatLe.
split with (fun n => S n).
unfold NatLe, leq; intros; omega.
Defined.

Instance timesTwo : HomPros NatLe NatLe.
split with (fun n => 2 * n).
simpl; intros; omega.
Defined.

Axiom fn_ext_pros : forall (A B : Pros') (f : Hom A B) (g : Hom A B),
    f = g <-> forall x : A, f x = g x.

Theorem Pros_mon_inj : forall (A B : Pros') (f : Hom A B),
    Mon f <-> injective f.
unfold Mon, injective; split; intros.
(* Trivial: use the property that Pros is a contruct over Set. *)
Focus 2.
rewrite fn_ext_pros; intro x. apply H.
generalize x; rewrite fn_ext_pros in H0. assumption.
admit.


Definition lst `(A : Pros) (a : A) : Prop := forall a' : A, a ≤ a'.

Theorem lst_NatLe : lst NatLe 0.
unfold lst; simpl; intros; omega.
Qed.

Instance exp : HomPros NatLe NatLe.
split with (fun n => 2 ^ n).
simpl; intros. induction a, a'; simpl. trivial.
rewrite plus_0_r. SearchPattern (_ ^ _ = _).