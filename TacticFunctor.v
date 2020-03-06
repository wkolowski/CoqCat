Require Import Cat.
Require Import Cat.Functor.

Set Implicit Arguments.

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

Fixpoint expDenote {C : Cat} {X Y : Ob C} (e : exp C X Y)
    : Hom X Y :=
match e with
    | Id X => id X
    | Var f => f
    | Comp e1 e2 => expDenote e1 .> expDenote e2
    | Fmap F e' => fmap F (expDenote e')
end.

Class Reify {C : Cat} {X Y : Ob C} (f : Hom X Y) : Type :=
{
    reify : exp C X Y;
    reify_spec : expDenote reify == f
}.

Arguments reify {C X Y} _ {Reify}.

#[refine]
Instance ReifyId (C : Cat) (X : Ob C) : Reify (id X) | 0 :=
{
    reify := Id X
}.
Proof.
  cbn. reflexivity.
Defined.

#[refine]
Instance ReifyComp (C : Cat) (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z)
    (R1 : Reify f) (R2 : Reify g) : Reify (f .> g) | 0 :=
{
    reify := Comp (reify f) (reify g)
}.
Proof.
  cbn. rewrite !reify_spec. reflexivity.
Defined.

#[refine]
Instance ReifyFmap (C D : Cat) (X Y : Ob C) (F : Functor C D) (f : Hom X Y)
    (R : Reify f) : @Reify D (fob F X) (fob F Y) (fmap F f) | 0 :=
{
    reify := Fmap F (reify f)
}.
Proof.
  cbn. rewrite reify_spec. reflexivity.
Defined.

#[refine]
Instance ReifyVar (C : Cat) (X Y : Ob C) (f : Hom X Y)
    : Reify f | 1 :=
{
    reify := Var f
}.
Proof.
  cbn. reflexivity.
Defined.

Class Simplify {C : Cat} {X Y : Ob C} (e : exp C X Y) : Type :=
{
    simplify : exp C X Y;
    simplify_spec : expDenote simplify == expDenote e
}.

Arguments simplify {C X Y} _ {Simplify}.

#[refine]
Instance NoSimplify (C : Cat) (X Y : Ob C) (e : exp C X Y)
    : Simplify e | 100 :=
{
    simplify := e
}.
Proof. reflexivity. Defined.

#[refine]
Instance SimplifyCompIdL (C : Cat) (X Y : Ob C) (e : exp C X Y)
  (S : Simplify e) : Simplify (Comp (Id X) e) | 1 :=
{
    simplify := simplify e
}.
Proof.
  cbn. rewrite simplify_spec. rewrite id_left. reflexivity.
Defined.

#[refine]
Instance SimplifyCompIdR (C : Cat) (X Y : Ob C) (e : exp C X Y)
  (S : Simplify e) : Simplify (Comp e (Id Y)) | 1 :=
{
    simplify := simplify e
}.
Proof.
  cbn. rewrite simplify_spec. rewrite id_right. reflexivity.
Defined.

#[refine]
Instance SimplifyCompRec (C : Cat) (X Y Z : Ob C)
  (e1 : exp C X Y) (e2 : exp C Y Z) (S1 : Simplify e1) (S2 : Simplify e2)
  : Simplify (Comp e1 e2) | 50 :=
{
    simplify := Comp (simplify e1) (simplify e2)
}.
Proof.
  cbn. rewrite !simplify_spec. reflexivity.
Defined.

#[refine]
Instance SimplifyFmapId (C D : Cat) (X : Ob C) (F : Functor C D)
  : Simplify (Fmap F (Id X)) :=
{
    simplify := Id (fob F X)
}.
Proof.
  cbn. rewrite pres_id. reflexivity.
Defined.

Inductive HomList {C : Cat} : Ob C -> Ob C -> Type :=
    | HomNil : forall X : Ob C, HomList X X
    | HomCons : forall X Y Z : Ob C,
        Hom X Y -> HomList Y Z -> HomList X Z.

Arguments HomNil  {C} _.
Arguments HomCons {C X Y Z} _ _.

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

Fixpoint Hmap {C D : Cat} {X Y : Ob C} (F : Functor C D) (l : HomList X Y)
  : HomList (fob F X) (fob F Y) :=
match l with
    | HomNil X => HomNil (fob F X)
    | HomCons h t => HomCons (fmap F h) (Hmap F t)
end.

Lemma expDenoteHL_Hmap_Happ :
  forall (C D : Cat) (X Y Z : Ob C) (F : Functor C D) (l1 : HomList X Y)
  (l2 : HomList Y Z),
    expDenoteHL (Hmap F (l1 +++ l2)) ==
    expDenoteHL (Hmap F l1 +++ Hmap F l2).
Proof.
  induction l1; cbn; intros.
    reflexivity.
    rewrite IHl1. reflexivity.
Qed.

Fixpoint flatten {C : Cat} {X Y : Ob C} (e : exp C X Y)
    : HomList X Y :=
match e with
    | Id X => HomNil X
    | Var f => HomCons f (HomNil _)
    | Comp e1 e2 => flatten e1 +++ flatten e2
    | Fmap F e' => Hmap F (flatten e')
end.

Lemma expDenoteHL_app :
  forall (C : Cat) (X Y Z : Ob C) (l1 : HomList X Y) (l2 : HomList Y Z),
    expDenoteHL (l1 +++ l2) == expDenoteHL l1 .> expDenoteHL l2.
Proof.
  induction l1; cbn; intros.
    rewrite id_left. reflexivity.
    assocr. rewrite IHl1. reflexivity.
Qed.

(*
Lemma expDenoteHL_fmap :
  forall (C D : Cat) (X Y : Ob C) (F : Functor C D) (e : exp C X Y),
    expDenoteHL (Hmap F (flatten e)) == expDenote (Fmap F e).
Proof.
  induction e; cbn.
    rewrite pres_id. reflexivity.
    rewrite id_right. reflexivity.
    rewrite expDenoteHL_Hmap_Happ, expDenoteHL_app, IHe1, IHe2. cbn.
      rewrite pres_comp. reflexivity.
    (*rewrite IHe.*)
Abort.
*)

Lemma expDenoteHL_fmap :
  forall (C D : Cat) (X Y : Ob C) (F : Functor C D) (l : HomList X Y),
    expDenoteHL (Hmap F l) == fmap F (expDenoteHL l).
Proof.
  induction l as [| h t]; cbn.
    rewrite pres_id. reflexivity.
    rewrite pres_comp, IHl. reflexivity.
Qed.

Theorem flatten_correct :
  forall (C : Cat) (X Y : Ob C) (e : exp C X Y),
    expDenoteHL (flatten e) == expDenote e.
Proof.
  induction e; cat.
    rewrite expDenoteHL_app, IHe1, IHe2. reflexivity.
    rewrite expDenoteHL_fmap, IHe. reflexivity.
Qed.

Theorem cat_reflect :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp C X Y),
    expDenoteHL (flatten (simplify e1)) ==
    expDenoteHL (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  intros. rewrite !flatten_correct, !simplify_spec in H. assumption.
Qed.

Ltac reflect_cat := intros;
match goal with
    | |- ?f == ?g =>
        do 2 (rewrite <- reify_spec, <- simplify_spec at 1; symmetry); cbn
end.

Ltac flat_reflect_cat := intros;
match goal with
    | |- ?f == ?g =>
        do 2 (rewrite <- reify_spec, <- simplify_spec at 1; symmetry);
        apply cat_reflect; cbn; rewrite !id_right
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
  repeat reflect_cat. reflexivity.
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
  flat_reflect_cat. reflexivity.
Qed.

Goal forall (C : Cat) (X Y Z W V T: Ob C) (f : Hom X Y) (g : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T),
      ((f .> (g .> h)) .> i) .> j == f .> g .> h .> i .> j.
Proof.
  flat_reflect_cat. reflexivity.
Qed.

Goal
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T), f == f' ->
      ((f .> (g .> h)) .> i) .> j == f' .> g .> h .> i .> j.
Proof.
  flat_reflect_cat. rewrite H. reflexivity.
Qed.

Goal
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g g' : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T), f .> g == f' .> g' ->
      ((f .> (g .> h)) .> i) .> j == f' .> (g' .> h) .> i .> j.
Proof.
  flat_reflect_cat. assocl. rewrite H. flat_reflect_cat. reflexivity.
Qed.

Goal
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g g' : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T),
      f == f .> id _ .> id _.
Proof.
  reflect_cat. reflexivity.
Qed.

End Test.