Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Cat.

Definition ProdMakerOb (C : Cat) (A B : Ob C) : Type :=
    {X : Ob C & {f : Hom X A & Hom X B}}.

Ltac pmob X := try intros until X;
match type of X with
  | ProdMakerOb _ _ _ => 
    let a := fresh X "_f" in
    let b := fresh X "_g" in destruct X as [X [a b]]
  | Ob _ => progress simpl in X; pmob X
end; simpl in *.

Ltac pmobs := repeat
match goal with
  | X : ProdMakerOb _ _ _ |- _ => pmob X
  | X : Ob _ |- _ => pmob X
end.

Definition ProdMakerHom {C : Cat} {A B : Ob C} (X Y : ProdMakerOb C A B)
    : Type.
Proof.
  pmobs.
  exact {h : Hom X Y | X_f == h .> Y_f /\ X_g == h .> Y_g}.
Defined.

Ltac pmhom f := try intros until f;
match type of f with
  | ProdMakerHom _ _ =>
      let a := fresh f "_eq1" in
      let b := fresh f "_eq2" in destruct f as [f [a b]]
  | Hom _ _ => progress simpl in f; pmhom f
end; simpl in f.

Ltac pmhoms := intros; repeat
match goal with
  | f : ProdMakerHom _ _ |- _ => pmhom f
  | f : Hom _ _ |- _ => pmhom f
  | _ => idtac
end.

(* TODO : finish tactics *)

Definition ProdMakerEquiv {C : Cat} {A B : Ob C} (P1 P2 : ProdMakerOb C A B)
    (h h' : ProdMakerHom P1 P2) : Prop.
Proof.
  pmobs. simpl in *. pmhom h. destruct h as [a [b c]]. pmhom h.
    destruct P1 as [X [f g]], P2 as [X' [f' g']];
    destruct h as [h _], h' as [h' _]. exact (h == h').
Defined.

Instance ProdMakerHomSetoid {C : Cat} {A B : Ob C} (P1 P2 : ProdMakerOb C A B)
    : Setoid (ProdMakerHom P1 P2) :=
{
    equiv := ProdMakerEquiv P1 P2
}.
Proof.
  solve_equiv; unfold ProdMakerEquiv;
  destruct P1 as [X [f g]], P2 as [X' [f' g']]; my_simpl; simpl in *.
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

(* TODO : prove this is equvalent to the usual products *)