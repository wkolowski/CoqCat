Require Import Cat.
Require Import Cat.Functor.

Set Implicit Arguments.

From Equations Require Import Equations.

Inductive exp {C : Cat} : Ob C -> Ob C -> Type :=
    | Id : forall X : Ob C, exp X X
    | Var : forall X Y : Ob C, Hom X Y -> exp X Y
    | Comp : forall X Y Z : Ob C,
        exp X Y -> exp Y Z -> exp X Z.

Arguments Id   {C} _.
Arguments Var  {C X Y} _.
Arguments Comp {C X Y Z} _ _.

Hint Constructors exp.

Equations expDenote {C : Cat} {X Y : Ob C} (e : exp X Y) : Hom X Y :=
expDenote (Id X)  := id X;
expDenote (Var f) := f;
expDenote (Comp e1 e2) := expDenote e1 .> expDenote e2.

Inductive HomList {C : Cat} : Ob C -> Ob C -> Type :=
    | HomNil : forall X : Ob C, HomList X X
    | HomCons : forall X Y Z : Ob C,
        Hom X Y -> HomList Y Z -> HomList X Z.

Arguments HomNil [C] _.
Arguments HomCons [C X Y Z] _ _.

Equations expDenoteHL {C : Cat} {X Y : Ob C} (l : HomList X Y) : Hom X Y :=
expDenoteHL (HomNil X) := id X;
expDenoteHL (HomCons h t) := h .> expDenoteHL t.

Equations Happ
  {C : Cat} {X Y Z : Ob C} (l1 : HomList X Y) (l2 : HomList Y Z)
  : HomList X Z :=
Happ (HomNil _) l2 := l2;
Happ (HomCons h t) l2 := HomCons h (Happ t l2).

Infix "+++" := (Happ) (at level 40).

Equations flatten {C : Cat} {X Y : Ob C} (e : exp X Y) : HomList X Y :=
flatten (Id X) := HomNil X;
flatten (Var f) := HomCons f (HomNil _);
flatten (Comp e1 e2) := flatten e1 +++ flatten e2.

Lemma expDenoteHL_comp_app :
  forall (C : Cat) (X Y Z : Ob C) (l1 : HomList X Y) (l2 : HomList Y Z),
    expDenoteHL (l1 +++ l2) == expDenoteHL l1 .> expDenoteHL l2.
Proof.
  intros. funelim (Happ l1 l2); simp Happ expDenoteHL.
    rewrite id_left. reflexivity.
    rewrite H, comp_assoc. reflexivity.
Qed.

Theorem flatten_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenoteHL (flatten e) == expDenote e.
Proof.
  intros. funelim (flatten e); simp flatten expDenoteHL expDenote.
    reflexivity.
    rewrite id_right. reflexivity.
    rewrite expDenoteHL_comp_app, H, H0. reflexivity.
Qed.

Theorem cat_reflect :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenoteHL (flatten e1) == expDenoteHL (flatten e2) ->
      expDenote e1 == expDenote e2.
Proof.
  intros. rewrite <- flatten_correct, H, flatten_correct. reflexivity.
Qed.

Ltac reify mor :=
match mor with
    | id ?X => constr:(Id X)
    | ?f .> ?g =>
        let e1 := reify f in
        let e2 := reify g in constr:(Comp e1 e2)
    | ?f => match type of f with
        | Hom ?X ?Y => constr:(Var f)
        | _ => fail
    end
end.

Ltac reflect_cat := intros;
match goal with
    | |- ?f == ?g =>
        let e1 := reify f in
        let e2 := reify g in
          change (expDenote e1 == expDenote e2);
          apply cat_reflect; cbn
end.

Lemma test_id_l :
  forall (C : Cat) (X Y : Ob C) (f : Hom X Y),
    id X .> f == f.
Proof.
  reflect_cat. simp expDenoteHL. try reflexivity.
Qed.

Lemma test_id_r :
  forall (C : Cat) (X Y : Ob C) (f : Hom X Y),
    f .> id Y == f.
Proof.
  reflect_cat. try reflexivity.
Qed.


Goal forall (C : Cat) (X Y Z W V T: Ob C) (f : Hom X Y) (g : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T),
      ((f .> (g .> h)) .> i) .> j == f .> g .> h .> i .> j.
Proof.
  intros. reflect_cat. reflexivity.
Qed.

Goal
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T), f == f' ->
      ((f .> (g .> h)) .> i) .> j == f' .> g .> h .> i .> j.
Proof.
  intros. reflect_cat.
Abort.

Goal
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g g' : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T), f .> g == f' .> g' ->
      ((f .> (g .> h)) .> i) .> j == f' .> (g' .> h) .> i .> j.
Proof.
  intros. reflect_cat.
Abort.

Goal
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g g' : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T),
      f == f .> id _ .> id _.
Proof.
  intros. reflect_cat. reflexivity.
Qed.