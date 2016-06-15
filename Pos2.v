Require Import Omega.
Require Import ZArith.
Require Import NPeano.
Require Export Cat.
Require Import ProofIrrelevance.

Class Leq {A : Set} := leq : A -> A -> Prop.

Notation "a ≤ b" := (leq a b) (at level 50).

Class Pros {A : Set} {leq : Leq} : Type :=
{
    leq_refl : forall a : A, a ≤ a;
    leq_trans : forall a b c : A, a ≤ b -> b ≤ c -> a ≤ c
}.

Definition U `(P : Pros) : Set := A.

Instance LeqNat : @Leq nat.
exact le.
Defined.

Instance NatLe : @Pros nat LeqNat.
split; unfold leq, LeqNat; intros; omega.
Defined.

Generalizable Variables A B leqA leqB.
Class HomPros `(PA : @Pros A leqA) `(PB : @Pros B leqB) : Type :=
{
    f : A -> B;
    homo : forall a a' : A, a ≤ a' -> f a ≤ f a'
}.

Definition get_uni `(_ : Pros) := A.
Coercion get_uni : Pros >-> Sortclass.

Definition get_fun `(_ : HomPros) := f.
Coercion get_fun : HomPros >-> Funclass.

(*Definition HomPros2 `(PA : Pros) `(PB : Pros) : Type :=
    forall (f : U PA -> U PB), forall (a a' : U PA), a ≤ a' -> f a ≤ f a'.*)

Instance HomProsInst : @CatHom Pros.
split. intros. exact (HomPros A B).
Defined.

(*Instance HomProsInst2 : @CatHom Pros.
split. intros. exact (HomPros2 A B).
Defined.*)

Instance CompPros : @CatComp Pros HomProsInst.
split. intros A B C f g. unfold Hom, HomProsInst in *.
destruct f, g. split with (f := fun n => f1 (f0 n)).
intros. apply homo1. apply homo0. assumption.
Defined.

Instance IdPros : @CatId Pros HomProsInst.
split. intro. split with (f := (fun a => a)).
trivial.
Defined.

Instance ProsCat : @Cat Pros HomProsInst CompPros IdPros.
split; intros; [destruct f0, g, h | destruct f0 | destruct f0];
simpl; f_equal.
Defined.

(*Theorem Pros_mon_inj : forall (A B : Pros) (f : Hom A B),
    Mon f <-> injective f.
unfold Mon, injective; split; intros.
(* Trivial: use the property that Pros is a contruct over Set. *)
Focus 2. (*unfold comp, CompPros in H0. simpl in *.*)
rewrite fn_ext_axiom.
destruct f0, g, h.*)

(*Instance CompPros2 : @CatComp Pros HomProsInst2.
split. intros. unfold Hom, HomProsInst2, HomPros2 in *.
intros f a a' H.
destruct (H ).*)


(*Definition HomPros {A B : Set} `(PA : Pros) `(PB : Pros) : Type :=
    {f : A -> B | forall a a' : A, a ≤ a' -> f a ≤ f a'}.

Instance addOne : @HomPros NatLe NatLe.
exact (fun n : nat => n + 1).

Definition HomPros `{A : Pros} `{B : Pros} (f : U A -> U B) : Prop :=
    forall a a' : U A, a ≤ a' -> f a ≤ f a'.

Definition *)

Definition lst `{A : Pros} (a : A) : Prop := forall a' : A, a ≤ a'.

Theorem hom_pres_lst : forall `(A : Pros) `(B : Pros) (f : U A -> U B) (a : U A),
    HomPros f -> lst a -> lst (f a).
unfold HomPros, lst in  *; intros.
