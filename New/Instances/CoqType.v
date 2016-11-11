Add LoadPath "/home/zeimer/Code/Coq/CoqCat/New".

Require Import Cat.

Require Import InitTerm.
Require Import BinProdCoprod.

Instance CoqType : Cat.
refine
{|
    Ob := Type;
    Hom := fun A B : Type => A -> B;
    comp := fun (A B C : Type) (f : A -> B) (g : B -> C) =>
      fun a : A => g (f a);
    id := fun (A : Type) (a : A) => a
|};
cat.
Defined.