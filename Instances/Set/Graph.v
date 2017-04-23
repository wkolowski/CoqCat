Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Class Graph : Type :=
{
    vertices : Type;
    edges : Type;
    src : edges -> vertices;
    tgt : edges -> vertices;
}.

Definition HomGraph (X Y : Graph) : Type :=
    {fv : @vertices X -> @vertices Y &
    {fe : @edges X -> @edges Y | forall e : @edges X,
        src (fe e) = fv (src e) /\
        tgt (fe e) = fv (tgt e)}}.

(* TODO: finish *)
(* TODO: define free category *)