Require Import Cat.
Require Import Cat.Functor.

Set Implicit Arguments.

From Equations Require Import Equations.

Inductive exp : forall C : Cat, Ob C -> Ob C -> Type :=
    | Id : forall (C : Cat) (X : Ob C), exp C X X
    | Var : forall (C : Cat) (X Y : Ob C), Hom X Y -> exp C X Y
    | Comp : forall (C : Cat) (X Y Z : Ob C),
        exp C X Y -> exp C Y Z -> exp C X Z
    | Fmap : forall (C D : Cat) (X Y : Ob C) (F : Functor C D),
        exp C X Y -> exp D (fob F X) (fob F Y).

Arguments Id   {C} _.
Arguments Var  {C X Y} _.
Arguments Comp {C X Y Z} _ _.
Arguments Fmap {C D X Y} _ _.

Hint Constructors exp.

Equations denote {C : Cat} {X Y : Ob C} (e : exp C X Y) : Hom X Y :=
denote (Id X)  := id X;
denote (Var f) := f;
denote (Comp e1 e2) := denote e1 .> denote e2;
denote (Fmap F e) := fmap F (denote e).

Inductive HomList {C : Cat} : Ob C -> Ob C -> Type :=
    | HomNil : forall X : Ob C, HomList X X
    | HomCons : forall X Y Z : Ob C,
        Hom X Y -> HomList Y Z -> HomList X Z.

Arguments HomNil {C} _.
Arguments HomCons {C X Y Z} _ _.

Equations denoteHL {C : Cat} {X Y : Ob C} (l : HomList X Y) : Hom X Y :=
denoteHL (HomNil X) := id X;
denoteHL (HomCons h t) := h .> denoteHL t.

Equations Happ
  {C : Cat} {X Y Z : Ob C} (l1 : HomList X Y) (l2 : HomList Y Z)
  : HomList X Z :=
Happ (HomNil _) l2 := l2;
Happ (HomCons h t) l2 := HomCons h (Happ t l2).

Infix "+++" := (Happ) (at level 40).

Equations Hfmap 
  {C D : Cat} (F : Functor C D)
  {X Y : Ob C} (l : HomList X Y) : HomList (fob F X) (fob F Y) :=
Hfmap F (HomNil _) := HomNil _;
Hfmap F (HomCons h t) := HomCons (fmap F h) (Hfmap F t).

Equations flatten {C : Cat} {X Y : Ob C} (e : exp C X Y) : HomList X Y :=
flatten (Id X) := HomNil X;
flatten (Var f) := HomCons f (HomNil _);
flatten (Comp e1 e2) := flatten e1 +++ flatten e2;
flatten (Fmap F e') := Hfmap F (flatten e').

Lemma denoteHL_Happ :
  forall (C : Cat) (X Y Z : Ob C) (l1 : HomList X Y) (l2 : HomList Y Z),
    denoteHL (l1 +++ l2) == denoteHL l1 .> denoteHL l2.
Proof.
  intros. funelim (Happ l1 l2); simp Happ denoteHL.
    rewrite id_left. reflexivity.
    rewrite H, comp_assoc. reflexivity.
Qed.

Lemma denoteHL_Hfmap :
  forall (C D : Cat) (F : Functor C D) (X Y : Ob C) (l : HomList X Y),
    denoteHL (Hfmap F l) == fmap F (denoteHL l).
Proof.
  intros. funelim (Hfmap F l); simp Hfmap denoteHL.
    rewrite pres_id. reflexivity.
    rewrite pres_comp, H. reflexivity.
Qed.

Lemma flatten_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp C X Y),
    denoteHL (flatten e) == denote e.
Proof.
  intros. funelim (flatten e); simp flatten denoteHL denote.
    reflexivity.
    rewrite id_right. reflexivity.
    rewrite denoteHL_Happ, H, H0. reflexivity.
    rewrite denoteHL_Hfmap, H. reflexivity.
Qed.

Theorem cat_reflect :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp C X Y),
    denoteHL (flatten e1) == denoteHL (flatten e2) ->
      denote e1 == denote e2.
Proof.
  intros. rewrite <- flatten_correct, H, flatten_correct. reflexivity.
Qed.

Ltac reify mor :=
match mor with
    | id ?X => constr:(Id X)
    | ?f .> ?g =>
        let e1 := reify f in
        let e2 := reify g in constr:(Comp e1 e2)
    | fmap ?F ?f =>
        let e := reify f in constr:(Fmap F e)
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
          change (denote e1 == denote e2);
          apply cat_reflect;
          repeat (simp flatten || simp Happ || simp denoteHL);
          rewrite ?id_right
end.

Section Test.

Variables
  (C D : Cat)
  (X Y Z V W T : Ob C)
  (F : Functor C D)
  (f f' : Hom X Y) (g g' : Hom Y Z) (h h' : Hom Z W)
  (i i' : Hom W V) (j j' : Hom V T).

Lemma test_id_l :
  id X .> f == f.
Proof.
  reflect_cat. reflexivity.
Qed.

Lemma test_id_r :
  f .> id Y == f.
Proof.
  reflect_cat. reflexivity.
Qed.

Lemma test_comp_id_l_many :
  id X .> id X .> f == f.
Proof.
  reflect_cat. reflexivity.
Qed.

Lemma test_comp_id_r_many :
  f .> id Y .> id Y == f.
Proof.
  reflect_cat. reflexivity.
Qed.

Lemma test_fmap_id :
  fmap F (id X) == id (fob F X).
Proof.
  reflect_cat. reflexivity.
Qed.

Lemma test_assoc :
  (f .> g) .> h == f .> (g .> h).
Proof.
  reflect_cat. reflexivity.
Qed.

Goal
  ((f .> (g .> h)) .> i) .> j == f .> g .> h .> i .> j.
Proof.
  reflect_cat. reflexivity.
Qed.

Goal
  f == f' ->
    ((f .> (g .> h)) .> i) .> j == f' .> g .> h .> i .> j.
Proof.
  intro. rewrite <- H. reflect_cat. reflexivity.
Qed.

Goal
  f .> g == f' .> g' ->
    ((f .> (g .> h)) .> i) .> j == f' .> (g' .> h) .> i .> j.
Proof.
  intros. reflect_cat.
Abort.

End Test.