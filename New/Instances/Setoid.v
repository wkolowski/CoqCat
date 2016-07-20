Require Import Cat.

Require Export Coq.Classes.SetoidClass.

Record Setoid' : Type :=
{
    carrier_ :> Type;
    setoid_ :> Setoid carrier_
}.
Print equiv.

Record HomSetoid (A B : Setoid') : Type :=
{
    f_ : A -> B;
    f_Proper : Proper ((@equiv _ A ==> (@equiv _ B))) f_
}.

Instance CoqSetoid : Cat :=
{|
    Ob := Setoid';
    Hom := HomSetoid;
|}.
intros.
(* Composition *) destruct X, X0. refine {| f_ := fun a : A => f_1 (f_0 a) |}.
unfold Proper, respectful; intros. f_equiv. rewrite H. reflexivity.
(* Identity *) intro. refine {| f_ := fun a : A => a |}.
unfold Proper, respectful. trivial.
(* comp_assoc *) intros. destruct f, g, h. f_equal.
(* id_left *) intros; destruct f; f_equal; apply proof_irrelevance.
(* id_right *) intros; destruct f; f_equal; apply proof_irrelevance.
Defined.




