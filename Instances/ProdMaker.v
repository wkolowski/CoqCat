Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Cat.

Set Universe Polymorphism.
Print sigT.
Definition ProdMakerOb (C : Cat) (A B : Ob C) : Type :=
    {X : Ob C & {f : Hom X A & Hom X B}}.

Definition ProdMakerHom {C : Cat} {A B : Ob C} (P1 P2 : ProdMakerOb C A B)
    : Type.
Proof.
  destruct P1 as [X [f g]], P2 as [X' [f' g']].
  exact {h : Hom X X' | f == h .> f' /\ g == h .> g'}.
Defined.
Print ProdMakerHom.

Definition ProdMakerEquiv {C : Cat} {A B : Ob C} (P1 P2 : ProdMakerOb C A B)
    (h h' : ProdMakerHom P1 P2) : Prop.
Proof.
    destruct P1 as [X [f g]], P2 as [X' [f' g']];
    destruct h as [h _], h' as [h' _]. exact (h == h').
Defined.

Instance ProdMakerHomSetoid {C : Cat} {A B : Ob C} (P1 P2 : ProdMakerOb C A B)
    : Setoid (ProdMakerHom P1 P2) :=
{
    equiv := ProdMakerEquiv P1 P2
}.
Proof.
  unfold ProdMakerEquiv; destruct P1 as [X [f g]], P2 as [X' [f' g']];
  cat; red; intros;
  repeat match goal with
    | x : ?sig _ _ |- _ => destruct x
  end.
    reflexivity.
    symmetry. assumption.
    rewrite H, H0. reflexivity.
Defined.

Definition ProdMakerComp {C : Cat} {A B : Ob C} (P1 P2 P3 : ProdMakerOb C A B)
    (h : ProdMakerHom P1 P2) (h' : ProdMakerHom P2 P3) : ProdMakerHom P1 P3.
Proof.
  unfold ProdMakerOb, ProdMakerHom in *;
  destruct P1 as [X1 [f1 g1]], P2 as [X2 [f2 g2]], P3 as [X3 [f3 g3]].
  destruct h as [h [h_eq1 h_eq2]], h' as [h' [h'_eq1 h'_eq2]].
  exists (h .> h'). split; cat.
    rewrite <- h'_eq1. cat.
    rewrite <- h'_eq2. cat.
Defined.

Definition ProdMakerId {C : Cat} {A B : Ob C} (P : ProdMakerOb C A B)
    : ProdMakerHom P P.
Proof.
  destruct P as [X [f g]]; simpl.
  exists (id X). cat.
Defined.

Instance ProdMaker (C : Cat) (A B : Ob C) : Cat :=
{
    Ob := ProdMakerOb C A B;
    Hom := ProdMakerHom;
    HomSetoid := ProdMakerHomSetoid;
    comp := ProdMakerComp;
    id := ProdMakerId
}.
Proof.
  repeat red.
  all: unfold ProdMakerOb, ProdMakerHom, ProdMakerComp, ProdMakerId,
  ProdMakerEquiv; intros;
  repeat match goal with
    | x : ?sig _ _ |- _ => destruct x
  end; simpl in *; cat.
    rewrite H, H0. reflexivity.
Defined.