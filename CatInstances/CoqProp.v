Add LoadPath "/home/Zeimer/Code/Coq/Cat".

Require Import ProofIrrelevance.

Require Import CatInstances.
Require Import InitTerm.
Require Import BinProdCoprod.

Instance HomProp : @CatHom Prop.
split. exact(fun A B : Prop => A -> B).
Defined.

Instance CompProp : @CatComp Prop HomProp.
split. exact (fun A B C : Prop => fun (f : A -> B) (g : B -> C) =>
    fun a : A => g (f a)).
Defined.

Instance IdProp : @CatId Prop HomProp.
split. exact (fun A : Prop => fun a : A => a).
Defined.

Instance CatProp : Cat Prop HomProp CompProp IdProp.
split; trivial.
Defined.

Theorem CoqProp_iso_iff : forall (P Q : Prop), P ~ Q <-> (P <-> Q).
unfold isomorphic, Iso; split; intros.
destruct H as [f [g _]]; split; assumption.
destruct H as [f g]. exists f, g. split;
simpl; apply proof_irrelevance.
Qed.

Theorem CoqProp_product_and : forall (P Q : Prop),
    is_product (P /\ Q) (@proj1 P Q) (@proj2 P Q).
unfold is_product; intros.
exists (fun x : X => conj (f x) (g x));
split; [split | intros]; simpl; apply proof_irrelevance.
Qed.
Print or.
Theorem CoqProp_coproduct_or : forall (P Q : Prop),
    is_coproduct (P \/ Q) (@or_introl P Q) (@or_intror P Q).
unfold is_coproduct; intros.
exists (
    fun x : P \/ Q => match x with
        | or_introl p => f p
        | or_intror q => g q
    end);
split; [split | intros]; simpl; apply proof_irrelevance.
Qed.