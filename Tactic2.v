Require Import Cat.
Require Import Cat.Functor.

Set Implicit Arguments.

Inductive exp {C : Cat} : Ob C -> Ob C -> Type :=
    | Id : forall X : Ob C, exp X X
    | Var : forall X Y : Ob C, Hom X Y -> exp X Y
    | Comp : forall X Y Z : Ob C,
        exp X Y -> exp Y Z -> exp X Z.

Arguments Id   {C} _.
Arguments Var  {C X Y} _.
Arguments Comp {C X Y Z} _ _.

Hint Constructors exp.

Fixpoint expDenote {C : Cat} {X Y : Ob C} (e : exp X Y)
    : Hom X Y :=
match e with
    | Id X => id X
    | Var f => f
    | Comp e1 e2 => expDenote e1 .> expDenote e2
end.

Fixpoint simplify {C : Cat} {X Y : Ob C} (e : exp X Y) {struct e} : exp X Y.
Proof.
  destruct e.
    exact (Id _).
    exact (Var h). destruct (simplify _ _ _ e1) as [| ? ? f1 | ? ? ? e11 e12]; clear e1.
      exact (simplify _ _ _ e2).
      destruct (simplify _ _ _ e2) as [| ? ? f2 | ? ? ? e21 e22]; clear e2.
        exact (Var f1).
        exact (Comp (Var f1) (Var f2)).
        exact (Comp (Var f1) (Comp e21 e22)).
      destruct (simplify _ _ _ e2) as [| ? ? f2 | ? ? ? e21 e22]; clear e2.
        exact (Comp e11 e12).
        exact (Comp (Comp e11 e12) (Var f2)).
        exact (Comp (Comp e11 e12) (Comp e21 e22)).
Defined.

Theorem simplify_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenote (simplify e) == expDenote e.
Proof.
  induction e; simpl; try reflexivity.
    destruct (simplify e1); destruct (simplify e2); simpl in *;
    try rewrite <- IHe1; try rewrite <- IHe2; cat.
Qed.

Inductive HomList {C : Cat} : Ob C -> Ob C -> Type :=
    | HomNil : forall X : Ob C, HomList X X
    | HomCons : forall X Y Z : Ob C,
        Hom X Y -> HomList Y Z -> HomList X Z.

Arguments HomNil [C] _.
Arguments HomCons [C X Y Z] _ _.

Fixpoint expDenoteHL {C : Cat} {X Y : Ob C} (l : HomList X Y)
    : Hom X Y :=
match l with
    | HomNil X => id X
    | HomCons h t => h .> expDenoteHL t
end.

Fixpoint Happ {C : Cat} {X Y Z : Ob C} (l1 : HomList X Y)
    : HomList Y Z -> HomList X Z :=
match l1 with
    | HomNil _ => fun l2 => l2
    | HomCons h t => fun l2 => HomCons h (Happ t l2)
end.

Infix "+++" := (Happ) (at level 40).

Fixpoint flatten {C : Cat} {X Y : Ob C} (e : exp X Y)
    : HomList X Y :=
match e with
    | Id X => HomNil X
    | Var f => HomCons f (HomNil _)
    | Comp e1 e2 => flatten e1 +++ flatten e2
end.

Lemma expDenoteHL_comp_app :
  forall (C : Cat) (X Y Z : Ob C) (l1 : HomList X Y) (l2 : HomList Y Z),
    expDenoteHL l1 .> expDenoteHL l2 == expDenoteHL (l1 +++ l2).
Proof.
  induction l1; simpl; intros.
    rewrite id_left. reflexivity.
    assocr. rewrite IHl1. reflexivity.
Qed.

Theorem flatten_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenoteHL (flatten e) == expDenote e.
Proof.
  induction e; cat.
    rewrite <- expDenoteHL_comp_app, IHe1, IHe2. reflexivity.
Qed.

Theorem cat_reflect :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenoteHL (flatten (simplify e1)) ==
    expDenoteHL (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  intros. rewrite !flatten_correct, !simplify_correct in H. assumption.
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
  reflect_cat. try reflexivity.
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
  intros. reflect_cat.
Abort.

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
  intros. reflect_cat.
Abort.

Fixpoint simplify' {C : Cat} {X Y : Ob C} (e : exp X Y) {struct e} : exp X Y :=
match e in (exp o o0) return (exp o o0) with
  | Id X0 => Id X0
  | Var h => Var h
  | @Comp _ X0 Y0 Z e1 e2 =>
    match simplify' e1 in (exp o o0)
    return (exp o o0 -> exp o0 Z -> exp o Z) with
      | Id X1 =>
          fun _ (e2 : exp X1 Z) => simplify' e2
      | @Var _ X1 Y1 f1 =>
          fun _ (e2 : exp Y1 Z) =>
          match simplify' e2 in (exp o o0)
          return (exp o o0 -> Hom X1 o -> exp X1 o0)
          with
          | Id X2 => fun _ (f1 : Hom X1 X2) => Var f1
          | @Var _ X2 Y2 f2 =>
              fun _ (f1 : Hom X1 X2) => Comp (Var f1) (Var f2)
          | @Comp _ X2 Y2 Z0 e21 e22 =>
              fun _ (f2 : Hom X1 X2) =>
              Comp (Var f2) (Comp e21 e22)
          end e2 f1
      | @Comp _ X1 Y1 Z0 e11 e12 =>
          fun _ (e2 : exp Z0 Z) =>
          match simplify' e2 in (exp o o0)
          return (exp o o0 -> exp Y1 o -> exp X1 o0)
          with
          | Id X2 => fun _ (e12 : exp Y1 X2) => Comp e11 e12
          | @Var _ X2 Y2 f2 =>
              fun _ (e12 : exp Y1 X2) =>
              Comp (Comp e11 e12) (Var f2)
          | @Comp _ X2 Y2 Z1 e21 e22 =>
              fun _ (e12 : exp Y1 X2) =>
              Comp (Comp e11 e12) (Comp e21 e22)
          end e2 e12
      end e1 e2
end.

Theorem simplify'_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenote (simplify' e) == expDenote e.
Proof.
  induction e; simpl; try reflexivity.
    destruct (simplify' e1); destruct (simplify' e2); simpl in *;
    try rewrite <- IHe1; try rewrite <- IHe2; cat.
Qed.