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

Definition limit {J C : Cat} {F : Functor J C}
    (K : Cone F) (del : forall K' : Cone F, ConeHom K' K)
    : Prop := @terminal (ConeCat F) K del.

Definition limit' {J C : Cat} {F : Functor J C} (K : Cone F) : Prop :=
    forall K' : Cone F, exists!! _ : ConeHom K' K, True.

Class Cocone {J C : Cat} (F : Functor J C) : Type :=
{
    coapex : Ob C;
    colegs : NatTrans F (ConstFunctor coapex J);
}.

Arguments coapex [J C F] _.
Arguments colegs [J C F] _.

Class CoconeHom {J C : Cat} {F : Functor J C}
    (C1 C2 : Cocone F) :=
{
    mor' : Hom (@coapex J C F C1) (@coapex J C F C2);
    cond' : forall X : Ob J,
        component (colegs C1) X .> mor' == component (colegs C2) X
}.

Arguments mor' [J C F C1 C2] _.
Arguments cond' [J C F C1 C2] _ _.

Instance CoconeHomSetoid {J C : Cat} {F : Functor J C}
    (C1 C2 : Cocone F) : Setoid (CoconeHom C1 C2) :=
{
    equiv := fun f g : CoconeHom C1 C2 => mor' f == mor' g
}.
Proof. solve_equiv. Defined.

Instance CoconeComp {J C : Cat} {F : Functor J C}
   (C1 C2 C3 : Cocone F) (f : CoconeHom C1 C2) (g : CoconeHom C2 C3)
    : CoconeHom C1 C3 :=
{
    mor' := mor' f .> mor' g
}.
Proof.
  intros. rewrite <- comp_assoc. rewrite cond'.
  destruct C2. destruct g. simpl in *. apply cond'0.
Defined.

Instance CoconeId {J C : Cat} {F : Functor J C}
   (C1 : Cocone F) : CoconeHom C1 C1 :=
{
    mor' := id (coapex C1)
}.
Proof. cat. Defined.

Instance CoconeCat {J C : Cat} (F : Functor J C) : Cat :=
{
    Ob := Cocone F;
    Hom := CoconeHom;
    HomSetoid := CoconeHomSetoid;
    comp := CoconeComp;
    id := CoconeId
}.
Proof. proper. all: cat. Defined.

Definition colimit {J C : Cat} {F : Functor J C}
    (K : Cocone F) (create : forall K' : Cocone F, CoconeHom K K')
    : Prop := @initial (CoconeCat F) K create.

Definition colimit' {J C : Cat} {F : Functor J C} (K : Cocone F) : Prop :=
    forall K' : Cocone F, exists!! _ : CoconeHom K K', True.

(* TODO : coherence conditions for (co)limits *)
(* TODO : continuous functors (see Bartosz Milewski's blog post from 2015/04/15 *)

(* TODO : kill the code below *)
Require Import Bool.

Instance Two : Cat :=
{
    Ob := bool;
    Hom := fun b b' : bool => if eqb b b' then True else False;
    HomSetoid := fun b b' : bool =>
      {| equiv := fun _ _ => True |}
}.
Proof.
  (* Equivalence *) solve_equiv.
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
