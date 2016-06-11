Require Import Omega.
Require Import ZArith.
Require Import NPeano.
Require Import Cat_alternativeFunctor.

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
split; intros. apply le_n. apply le_trans with b; assumption.
Defined.

(*Generalizable Variables A B leqA leqB.

Class HomPros `(PA : @Pros A leqA) `(PB : @Pros B leqB) : Type :=
{
    f : A -> B;
    homo : forall a a' : A, leqA a a' -> leqB (f a) (f a')
}.

Definition get_fun `(_ : HomPros) := f.

Coercion get_fun : HomPros >-> Funclass.

Definition HomPros2 `(PA : Pros) `(PB : Pros) : Type :=
    forall (f : U PA -> U PB), forall (a a' : U PA), a ≤ a' -> f a ≤ f a'.

Instance HomProsInst : @CatHom Pros.
split. intros. exact (HomPros A B). (* exact (@HomPros _ _ A _ _ B).*)
Defined.

Instance HomProsInst2 : @CatHom Pros.
split. intros. exact (HomPros2 A B).
Defined.

Instance CompPros : @CatComp Pros HomProsInst.
split. intros A B C f g. unfold Hom, HomProsInst in *.

Instance CompPros2 : @CatComp Pros HomProsInst2.
split. intros. unfold Hom, HomProsInst2, HomPros2 in *.
intros f a a' H.
destruct (H ).


Definition HomPros {A B : Set} `(PA : Pros) `(PB : Pros) : Type :=
    {f : A -> B | forall a a' : A, a ≤ a' -> f a ≤ f a'}.

Instance addOne : @HomPros NatLe NatLe.
exact (fun n : nat => n + 1).*)

Definition HomPros `{A : Pros} `{B : Pros} (f : U A -> U B) : Prop :=
    forall a a' : U A, a ≤ a' -> f a ≤ f a'.

Definition 

Definition lst `{A : Pros} (a : U A) : Prop := forall a' : U A, a ≤ a'.

Theorem hom_pres_lst : forall `(A : Pros) `(B : Pros) (f : U A -> U B) (a : U A),
    HomPros f -> lst a -> lst (f a).
unfold HomPros, lst in  *; intros.
