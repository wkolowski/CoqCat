From Equations Require Import Equations.

From Cat Require Import Cat.

Set Implicit Arguments.

Inductive exp {C : Cat} : Ob C -> Ob C -> Type :=
| Id   : forall X : Ob C, exp X X
| Var  : forall X Y : Ob C, Hom X Y -> exp X Y
| Comp : forall X Y Z : Ob C, exp X Y -> exp Y Z -> exp X Z.

Arguments Id   {C} _.
Arguments Var  {C X Y} _.
Arguments Comp {C X Y Z} _ _.

#[global] Hint Constructors exp : core.

Equations expDenote {C : Cat} {X Y : Ob C} (e : exp X Y) : Hom X Y :=
| Id X       => id X
| Var f      => f
| Comp e1 e2 => expDenote e1 .> expDenote e2.

Inductive HomList {C : Cat} : Ob C -> Ob C -> Type :=
| HomNil  : forall X : Ob C, HomList X X
| HomCons : forall X Y Z : Ob C, Hom X Y -> HomList Y Z -> HomList X Z.

Arguments HomNil [C] _.
Arguments HomCons [C X Y Z] _ _.

Equations expDenoteHL {C : Cat} {X Y : Ob C} (l : HomList X Y) : Hom X Y :=
| HomNil X    => id X
| HomCons h t => h .> expDenoteHL t.

Equations Happ
  {C : Cat} {X Y Z : Ob C} (l1 : HomList X Y) (l2 : HomList Y Z) : HomList X Z :=
| HomNil _   , l2 => l2
| HomCons h t, l2 => HomCons h (Happ t l2).

Infix "+++" := (Happ) (at level 40).

Equations flatten {C : Cat} {X Y : Ob C} (e : exp X Y) : HomList X Y :=
| Id X       =>  HomNil X
| Var f      => HomCons f (HomNil _)
| Comp e1 e2 => flatten e1 +++ flatten e2.

Lemma expDenoteHL_comp_app :
  forall (C : Cat) (X Y Z : Ob C) (l1 : HomList X Y) (l2 : HomList Y Z),
    expDenoteHL (l1 +++ l2) == expDenoteHL l1 .> expDenoteHL l2.
Proof.
  intros. funelim (Happ l1 l2); simp Happ expDenoteHL.
    now rewrite comp_id_l.
    now rewrite H, comp_assoc.
Qed.

Lemma flatten_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenoteHL (flatten e) == expDenote e.
Proof.
  intros. funelim (flatten e); simp flatten expDenoteHL expDenote.
    easy.
    now rewrite comp_id_r.
    now rewrite expDenoteHL_comp_app, H, H0.
Qed.

Lemma cat_reflect :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenoteHL (flatten e1) == expDenoteHL (flatten e2) ->
      expDenote e1 == expDenote e2.
Proof.
  now intros; rewrite <- flatten_correct, H, flatten_correct.
Qed.

Ltac reify mor :=
match mor with
| id ?X => constr:(Id X)
| ?f .> ?g =>
  let e1 := reify f in
  let e2 := reify g in constr:(Comp e1 e2)
| ?f =>
  match type of f with
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
  now reflect_cat.
Qed.

Lemma test_id_r :
  forall (C : Cat) (X Y : Ob C) (f : Hom X Y),
    f .> id Y == f.
Proof.
  now reflect_cat.
Qed.

Goal forall (C : Cat) (X Y Z W V T: Ob C) (f : Hom X Y) (g : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T),
      ((f .> (g .> h)) .> i) .> j == f .> g .> h .> i .> j.
Proof.
  now intros; reflect_cat.
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
  now intros; reflect_cat.
Qed.