Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Cat.

Inductive exp {C : Cat} : Ob C -> Ob C -> Type :=
    | Id : forall X : Ob C, exp X X
    | Var : forall X Y : Ob C, Hom X Y -> exp X Y
    | Comp : forall X Y Z : Ob C,
        exp X Y -> exp Y Z -> exp X Z.

Arguments Id [C] _.
Arguments Var [C X Y] _.
Arguments Comp [C X Y Z] _ _.

Fixpoint expDenote {C : Cat} {X Y : Ob C} (e : exp X Y)
    : Hom X Y :=
match e with
    | Id X => id X
    | Var f => f
    | Comp e1 e2 => expDenote e1 .> expDenote e2
end.

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

Lemma flatten_correct' :
  forall (C : Cat) (X Y Z : Ob C) (l1 : HomList X Y) (l2 : HomList Y Z),
    expDenoteHL l1 .> expDenoteHL l2 == expDenoteHL (l1 +++ l2).
Proof.
  induction l1; simpl; intros.
    rewrite id_left. reflexivity.
    assocr. rewrite IHl1. reflexivity.
Qed.

Theorem flatten_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenote e == expDenoteHL (flatten e).
Proof.
  induction e; cat.
    rewrite IHe1, IHe2. apply flatten_correct'.
Qed.

Theorem cat_reflect :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenoteHL (flatten e1) == expDenoteHL (flatten e2) ->
      expDenote e1 == expDenote e2.
Proof.
  induction e1; cat.
    rewrite flatten_correct. assumption.
    rewrite flatten_correct. assumption.
      rewrite <- flatten_correct' in H.
      do 3 rewrite <- flatten_correct in H. assumption.
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

Ltac mor' :=
match goal with
    | |- ?f == ?g =>
        let e1 := reify f in
        let e2 := reify g in
          change (expDenote e1 == expDenote e2);
          apply cat_reflect; simpl
end.

Ltac mor := intros; mor'; try reflexivity.

Ltac test := intros; mor'.

Theorem wut : forall (C : Cat) (X Y Z W V T: Ob C) (f : Hom X Y) (g : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T),
      ((f .> (g .> h)) .> i) .> j == f .> g .> h .> i .> j.
Proof.
  test. reflexivity.
Qed.

Ltac reify2 mor :=
match mor with
    | id ?X => constr:(Id X)
    | ?f =>
        match goal with
            | H : ?f == ?g |- _ => rewrite H in f
        end
    | ?f .> ?g =>
        let e1 := reify f in
        let e2 := reify g in constr:(Comp e1 e2)
    | ?f => match type of f with
        | Hom ?X ?Y => constr:(Var f)
        | _ => fail
    end
end.

Ltac mor2' :=
match goal with
    | H : ?h == ?h' |- context [?h] => rewrite H; mor2'
    | |- ?f == ?g =>
        let e1 := reify2 f in
        let e2 := reify2 g in
          change (expDenote e1 == expDenote e2);
          apply cat_reflect; simpl
end.

Ltac mor2 := intros; mor2'; try reflexivity.
Ltac test2 := intros; mor2'.


Theorem wut2 :
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T), f == f' ->
      ((f .> (g .> h)) .> i) .> j == f' .> g .> h .> i .> j.
Proof.
  test2. reflexivity.
Qed.

Theorem wut3 :
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g g' : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T), f .> g == f' .> g' ->
      ((f .> (g .> h)) .> i) .> j == f' .> (g' .> h) .> i .> j.
Proof.
  test2.
Abort.

Theorem wut4 :
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g g' : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T),
      f == f .> id _ .> id _.
Proof.
  test. reflexivity.
Abort.

Fixpoint simplify {C : Cat} {X Y : Ob C} (e : exp X Y) : exp X Y :=
match e with
    | Id X => Id X
    | Var f => Var f
    | Comp e1 e2 => Comp (simplify e1) (simplify e2)
end.

Fixpoint simplify' {C : Cat} {X Y : Ob C} (e : exp X Y) {struct e} : exp X Y.
Proof.
  destruct e.
    exact (Id X).
    exact (Var h).
    destruct (simplify' _ _ _ e1); clear e1.
      exact (simplify' _ _ _ e2).
      exact (Comp (Var h) (simplify' _ _ _ e2)).
      exact (Comp (Comp e3 e4) (simplify' _ _ _ e2)).
Defined.

Theorem simplify_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenote (simplify e) == expDenote e.
Proof.
  induction e; simpl; try rewrite IHe1, IHe2; reflexivity.
Qed.

Theorem simplify'_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenote (simplify' e) == expDenote e.
Proof.
  induction e; simpl; try reflexivity.
    destruct (simplify' e1); simpl in *;
    try rewrite <- IHe1; try rewrite IHe2; cat.
Qed.

Print simplify'.

Fixpoint simplify2 {C : Cat} {X Y : Ob C} (e : exp X Y) : exp X Y :=
match e in (exp o o0) return (exp o o0) with
  | Id A => Id A
  | Var f => Var f
  | @Comp _ A B C e1 e2 =>
      match simplify2 e1 in (exp A B) with
      (*return exp A B -> exp B C -> exp A C with*)
          | Id A => fun (_ : exp A A) (e2 : exp A C) => simplify2 e2
          | e1' => fun _ e2 => Comp e1' (simplify2 e2)
      end e1 e2
end.

Theorem simplify2_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y),
    expDenote (simplify2 e) == expDenote e.
Proof.
  induction e; simpl; try reflexivity.
    destruct (simplify2 e1); simpl in *;
    try rewrite <- IHe1; try rewrite IHe2; cat.
Qed.