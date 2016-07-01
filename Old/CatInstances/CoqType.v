Add LoadPath "/home/Zeimer/Code/Coq/Cat".

Require Import ProofIrrelevance.

Require Import CatInstances.
Require Import InitTerm.
Require Import BinProdCoprod.

Instance HomCoqType : @CatHom Type.
split. exact (fun A B : Type => A -> B).
Defined.

Instance CompCoqType : @CatComp Type HomCoqType.
split; exact (fun (A B C : Type) (f : Hom A B) (g : Hom B C) => fun a : A => g (f a)).
Defined.

Instance IdCoqType : @CatId Type HomCoqType.
split; exact (fun (A : Type) (a : A) => a).
Defined.

Instance CatCoqType : Cat Type HomCoqType CompCoqType IdCoqType.
split; trivial.
Defined.