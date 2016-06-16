Require Import Omega.
Require Import ProofIrrelevance.
Require Export Cat.

Class Sgr {A : Type} : Type :=
{
    op : A -> A -> A;
    op_assoc : forall a b c : A, op a (op b c) = op (op a b) c
}.

Notation "a & b" := (op a b) (at level 50).

Definition Sgr'_Sort `(_ : Sgr) := A.
Coercion Sgr'_Sort : Sgr >-> Sortclass.

Class HomSgr `(A : Sgr) `(B : Sgr) : Type :=
{
    f_ : A -> B;
    homo_sgr : forall a b : A, f_ (a & b) = f_ a & f_ b
}.

Theorem trolo : forall `(A : Sgr) (a : A), a = a.
intros. destruct A.
trivial. Qed.

Definition HomSgr'_Fun `(_ : HomSgr) := f_.
Coercion HomSgr'_Fun : HomSgr >-> Funclass.

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

Instance timesTwo : HomSgr NatPlus NatPlus.
split with (fun n => 2 * n).
simpl; intros.
assert (a + b + (a + b + 0) = a + (a + 0) + (b + (b + 0))). omega.
assumption.
Defined.