Add LoadPath "/home/Zeimer/Code/Coq/Cat".

Require Import ProofIrrelevance.

Require Export CatInstances.
Require Export Pros.

Class Pos {A : Type} : Type :=
{
    pros_ : @Pros A;
    wasym : forall x y : A, x ≤ y -> y ≤ x -> x = y
}.

Definition Pos_Pros `(_ : Pos) := pros_.
Coercion Pos_Pros : Pos >-> Pros.

Class Pos' : Type :=
{
    carrier_ : Type;
    pos_ : @Pos carrier_
}.

Definition Pos'_Pos (_ : Pos') := pos_.
Coercion Pos'_Pos : Pos' >-> Pos.

Instance HomPos : @CatHom Pos'.
split. intros. exact (HomPros A B).
Defined.

Instance CompPos : @CatComp Pos' HomPos.
split; intros A B C f g.
split with (fun a : A => g (f a)). destruct f, g; simpl.
intros. apply homo_pros0; apply homo_pros; assumption.
Defined.

Instance IdPos : @CatId Pos' HomPos.
split; intro; split with (fun a : A => a); trivial.
Defined.

Instance CatPos : @Cat Pos' HomPos CompPos IdPos.
split; unfold Hom, HomPos; simpl; intros; destruct f;
f_equal; apply proof_irrelevance.
Defined.

