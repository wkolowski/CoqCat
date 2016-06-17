Require Import Omega.
Require Import ProofIrrelevance.
Require Import List.
Require Import ZArith.

Require Export CatInstances.

Class Sgr {A : Type} : Type :=
{
    op : A -> A -> A;
    op_assoc : forall a b c : A, op a (op b c) = op (op a b) c
}.

Notation "a & b" := (op a b) (at level 50).

Definition Sgr_Sort `(_ : Sgr) := A.
Coercion Sgr_Sort : Sgr >-> Sortclass.

Class HomSgr `(A : Sgr) `(B : Sgr) : Type :=
{
    f_ : A -> B;
    homo_sgr : forall a b : A, f_ (a & b) = f_ a & f_ b
}.

Definition HomSgr_Fun `(_ : HomSgr) := f_.
Coercion HomSgr_Fun : HomSgr >-> Funclass.

Class Sgr' : Type :=
{
    carrier_ : Type;
    sgr_ : @Sgr carrier_
}.

Definition Sgr'_Sgr `(_ : Sgr') := sgr_.
Coercion Sgr'_Sgr : Sgr' >-> Sgr.

Instance HomSgr' : @CatHom Sgr'.
split. intros. exact (HomSgr A B).
Defined.

Instance CompSgr : @CatComp Sgr' HomSgr'.
split. intros A B C f g. unfold Hom, HomSgr' in *.
split with (fun a : A => g (f a)).
destruct f, g; intros. simpl. rewrite homo_sgr0, homo_sgr1; trivial.
Defined.

Instance IdSgr : @CatId Sgr' HomSgr'.
split; intros. split with (fun a : A => a). trivial.
Defined.

Instance CatSgr : @Cat Sgr' HomSgr' CompSgr IdSgr.
split; intros; destruct f; simpl; f_equal; apply proof_irrelevance.
Defined.

Instance NatPlus : @Sgr nat.
split with plus. intros; omega. (*rewrite plus_assoc; trivial. (* omega.*)*)
Defined.

Instance NatMult : @Sgr nat.
split with mult. intros.
assert (a * (b * c) = a * b * c). rewrite mult_assoc. trivial.
assumption.
Defined.

Instance ZPlus : @Sgr Z.
split with Zplus; intros; omega.
Defined.

Instance ZMult : @Sgr Z.
split with Zmult; intros. rewrite <- Zmult_assoc_reverse. trivial.
Defined.

Instance ListApp (A : Type) : @Sgr (list A).
split with (@app A).
intros; rewrite app_assoc; trivial.
Defined.

Instance timesTwo : HomSgr NatPlus NatPlus.
split with (fun n => 2 * n).
simpl; intros.
assert (a + b + (a + b + 0) = a + (a + 0) + (b + (b + 0))). omega.
assumption.
Defined.

Instance len (A : Type) : HomSgr (ListApp A) NatPlus.
split with (@length A).
induction a, b; simpl; trivial.
rewrite app_nil_r, plus_0_r. trivial.
f_equal. apply IHa.
Defined.

Print len.

Axiom fn_ext_sgr : forall (A B : Sgr') (f : Hom A B) (g : Hom A B),
    f = g <-> forall x : A, f x = g x.

(*Theorem sgr_mon_inj : forall (A B : Sgr') (f : Hom A B),
    Mon f <-> injective f.
unfold Mon, injective; split; intros.
(* Part 1 to be filled when concrete categories are developed. *)
Focus 2.
rewrite fn_ext_sgr; intro x. apply H.
generalize x; rewrite fn_ext_sgr in H0. assumption.
admit.*)

