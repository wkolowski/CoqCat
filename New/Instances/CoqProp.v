Add LoadPath "/home/zeimer/Code/Coq/CoqCat/New".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export FunctionalExtensionality.

Instance CoqProp : Cat.
refine
{|
    Ob := Prop;
    Hom := fun A B : Prop => A -> B;
    comp := fun (A B C : Prop) (f : A -> B) (g : B -> C) (a : A) => g (f a);
    id := fun (A : Prop) (a : A) => a
|};
cat.
Defined.

Theorem CoqProp_iso_iff : forall (P Q : Prop), P ~ Q <-> (P <-> Q).
unfold isomorphic, Iso; split; intros.
destruct H as [f [g _]]; split; assumption.
destruct H as [f g]. exists f, g. split;
simpl; apply proof_irrelevance.
Qed.

Theorem CoqProp_product_and : forall (P Q : Prop),
    product CoqProp (P /\ Q) (@proj1 P Q) (@proj2 P Q).
unfold product; intros.
exists (fun x : X => conj (f x) (g x));
split; [split | intros]; simpl; apply proof_irrelevance.
Qed.

Theorem CoqProp_coproduct_or : forall (P Q : Prop),
    coproduct CoqProp (P \/ Q) (@or_introl P Q) (@or_intror P Q).
unfold coproduct; intros.
exists (
    fun x : P \/ Q => match x with
        | or_introl p => f p
        | or_intror q => g q
    end);
split; [split | intros]; simpl; apply proof_irrelevance.
Qed.

Instance CoqProp_init : has_init CoqProp :=
{
  init := False
}.
Proof.
  red; simpl; intro. exists (fun x : False => match x with end).
  red; split; intros; auto. extensionality a. inversion a.
Defined.

Instance CoqProp_term : has_term CoqProp :=
{
  term := True
}.
Proof.
  red; simpl; intro. exists (fun _ => I).
  red; split; intros; auto. extensionality a. destruct (x' a). trivial.
Defined.


  