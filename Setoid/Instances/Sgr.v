Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

(*Require Export FunctionalExtensionality.
Require Import ClassicalFacts.*)

Set Universe Polymorphism.

Class Sgr : Type :=
{
    carrier : Type;
    op : carrier -> carrier -> carrier;
    assoc : forall x y z : carrier, op x (op y z) = op (op x y) z
}.

Coercion carrier : Sgr >-> Sortclass.

Definition SgrHom (A B : Sgr) : Type :=
    {f : A -> B | forall x y : A, f (op x y) = op (f x) (f y)}.

Definition SgrHom_Fun (A B : Sgr) (f : SgrHom A B) : A -> B := proj1_sig f.
Coercion SgrHom_Fun : SgrHom >-> Funclass.

Definition SgrComp (A B C : Sgr) (f : SgrHom A B) (g : SgrHom B C)
    : SgrHom A C.
Proof.
  red. destruct f as [f Hf], g as [g Hg].
  exists (fun a : A => g (f a)). intros. rewrite Hf, Hg. auto.
Defined.

Definition SgrId (A : Sgr) : SgrHom A A.
Proof. red. exists (fun a : A => a). auto. Defined.

Instance SgrCat : Cat :=
{
    Ob := Sgr;
    Hom := SgrHom;
    HomSetoid := fun X Y : Sgr =>
        {| equiv := fun f g : SgrHom X Y => forall x : X, f x = g x |};
    comp := SgrComp;
    id := SgrId
}.
Proof.
  (* Equivalence *) cat. red. intros. rewrite H, H0. auto.
  (* Proper *) repeat red; intros. destruct x, y, x0, y0; cat.
    rewrite H, H0. auto.
  (* Category laws *) all: intros; repeat match goal with
    | f : SgrHom _ _ |- _ => destruct f
  end; simpl; auto.
Defined.