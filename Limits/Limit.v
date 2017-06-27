Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Cat.
Require Import Cat.Functor.
Require Import Cat.NatTrans.
Require Import Cat.Limits.InitTerm.

Set Implicit Arguments.

Class Cone {J C : Cat} (F : Functor J C) : Type :=
{
    apex : Ob C;
    legs : NatTrans (ConstFunctor apex J) F;
}.

Arguments apex [J C F] _.
Arguments legs [J C F] _.

Class ConeHom {J C : Cat} {F : Functor J C}
    (C1 C2 : Cone F) :=
{
    mor : Hom (@apex J C F C1) (@apex J C F C2);
    cond : forall X : Ob J,
        mor .> component (legs C2) X == component (legs C1) X
}.

Arguments mor [J C F C1 C2] _.
Arguments cond [J C F C1 C2] _ _.

Instance ConeHomSetoid {J C : Cat} {F : Functor J C}
    (C1 C2 : Cone F) : Setoid (ConeHom C1 C2) :=
{
    equiv := fun f g : ConeHom C1 C2 => mor f == mor g
}.
Proof. solve_equiv. Defined.

Instance ConeComp {J C : Cat} {F : Functor J C}
   (C1 C2 C3 : Cone F) (f : ConeHom C1 C2) (g : ConeHom C2 C3)
    : ConeHom C1 C3 :=
{
    mor := mor f .> mor g
}.
Proof.
  intros. assocr. do 2 rewrite cond. reflexivity.
Defined.

Instance ConeId {J C : Cat} {F : Functor J C}
   (C1 : Cone F) : ConeHom C1 C1 :=
{
    mor := id (apex C1)
}.
Proof. cat. Defined.

Instance ConeCat {J C : Cat} (F : Functor J C) : Cat :=
{
    Ob := Cone F;
    Hom := ConeHom;
    HomSetoid := ConeHomSetoid;
    comp := ConeComp;
    id := ConeId
}.
Proof. proper. all: cat. Defined.

Check @terminal.

Definition limit {J C : Cat} {F : Functor J C}
    (K : Cone F) (del : forall K' : Cone F, ConeHom K' K)
    : Prop := @terminal (ConeCat F) K del.



Require Import Bool.

(* TODO : fix *)

Instance Two : Cat :=
{
    Ob := bool;
    Hom := fun b b' : bool => if eqb b b' then True else False
}.
Proof.
  (* Composition *) destruct A, B, C; simpl; tauto.
  (* Proper *) proper.
  (* Assoc *) cat.
  (* Id *) destruct A; simpl; tauto.
  (* Id laws *) all: cat.
Defined.

Instance DiagramProd (C : Cat) (X Y : Ob C)
    : Functor Two C :=
{
    fob := fun A : Ob Two => if A then X else Y;
}.
Proof.
  (* fmap *) destruct A, B; simpl; inversion 1.
    exact (id X).
    exact (id Y).
  destruct A, B; proper; cat.
  destruct A, B, C0; cat.
  destruct A; cat.
Defined.

Instance ProdCone_legs (C : Cat) (X : Ob C)
    : NatTrans (ConstFunctor X Two) (DiagramProd C X X) := {}.
Proof.
  (* component *) simpl. destruct X0; exact (id X).
  (* naturality *) destruct X0, Y, f; simpl; cat.
Defined.

Instance ProdCone (C : Cat) (X : Ob C)
    : Cone (DiagramProd _ X X) :=
{
    apex := X;
    legs := ProdCone_legs C X
}.

Eval simpl in  @apex Two Two (DiagramProd Two true true) (ProdCone Two true).
