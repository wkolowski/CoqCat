Require Import Cat.

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

Class PackedHom (C : Cat) : Type := mk
{
    dom : Ob C;
    cod : Ob C;
    mor : Hom dom cod;
}.

Arguments mk [C] _ _.
Arguments dom [C] _.
Arguments cod [C] _.

Require Import List.
Import ListNotations.

Fixpoint flatten {C : Cat} {X Y : Ob C} (e : exp X Y)
    : list (PackedHom C) :=
match e with
    | Id _ => []
    | @Var _ X Y f => [mk X Y f]
    | Comp e1 e2 => flatten e1 ++ flatten e2
end.

Inductive wf {C : Cat} : list (PackedHom C) -> Prop :=
    | wf_nil : wf []
    | wf_singl : forall f : PackedHom C, wf [f]
    | wf_app : forall l1 l2 : list (PackedHom C),
        wf l1 -> wf l2 -> wf (l1 ++ l2).

Hint Constructors wf.

Theorem flatten_wf :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y), wf (flatten e).
Proof.
  induction e; simpl; auto.
Qed.

Inductive wf' {C : Cat} : list (PackedHom C) -> Prop :=
    | wf'_nil : wf' []
    | wf'_singl : forall f : PackedHom C, wf' [f]
    | wf'_cons : forall (X : Ob C) (f g : PackedHom C)
        (l : list (PackedHom C)),
          cod f = dom g -> wf' (g :: l) -> wf' (f :: g :: l).

Hint Constructors wf'.

Lemma wf'_cod :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y) (h : PackedHom C)
  (t : list (PackedHom C)),
    flatten e = h :: t -> dom h = X.
Proof.
  induction e; inversion 1; cbn in *.
    auto.
    destruct e1; cbn in *; eauto.
    destruct (flatten e2).
      eapply IHe1. 
Restart.
  intros C X Y e. induction (flatten e) as [| h' t'].
    inversion 1.
Abort.

Theorem flatten_wf' :
  forall (C : Cat) (X Y : Ob C) (e : exp X Y), wf' (flatten e).
Proof.
  induction e; cbn; auto.
    induction (flatten e1); cbn; auto. destruct l.
      Focus 2. cbn. inversion IHe1; subst; auto.
      destruct (flatten e2); cbn in *; auto. constructor; auto.
Abort.

Theorem flatten_cons :
  forall (C : Cat) (h : PackedHom C) (t : list (PackedHom C)),
    wf (h :: t) -> wf t.
Proof.
  induction t; simpl; auto.
    inversion 1. subst.
Abort.

Theorem flatten_wf_inv :
  forall (C : Cat) (l l1 l2 : list (PackedHom C)),
    wf l -> l = l1 ++ l2 -> wf l1 /\ wf l2.
Proof.
  induction l as [| h t]; simpl; intros.
    destruct l1; simpl in *; inversion H0; auto.
    destruct l1; simpl in *; subst; auto.
      rewrite app_comm_cons in H0. inversion H0; subst.
      rewrite app_comm_cons in H. inversion H; subst. Focus 2.
      inversion H.
Abort.

(*Lemma expDenoteHL_comp_app :
  forall (C : Cat) (X Y Z : Ob C) (l1 : HomList X Y) (l2 : HomList Y Z),
    expDenoteHL l1 .> expDenoteHL l2 == expDenoteHL (l1 ++ l2).
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
    rewrite <- expDenoteHL_comp_app. 
Qed.

Theorem cat_reflect :
  forall (C : Cat) (X Y : Ob C) (e1 e2 : exp X Y),
    expDenoteHL (flatten (simplify e1)) ==
    expDenoteHL (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  intros. rewrite !flatten_correct, !simplify_correct in H.
  assumption.
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

Ltac mor' := intros;
match goal with
    | |- ?f == ?g =>
        let e1 := reify f in
        let e2 := reify g in
          change (expDenote e1 == expDenote e2);
          apply cat_reflect; simpl
end.

Ltac mor := mor'; reflexivity.

Goal forall (C : Cat) (X Y Z W V T: Ob C) (f : Hom X Y) (g : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T),
      ((f .> (g .> h)) .> i) .> j == f .> g .> h .> i .> j.
Proof.
  mor'. reflexivity.
Qed.

Goal
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T), f == f' ->
      ((f .> (g .> h)) .> i) .> j == f' .> g .> h .> i .> j.
Proof.
  mor'.
Restart.
  wuut.
Qed.

Goal
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g g' : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T), f .> g == f' .> g' ->
      ((f .> (g .> h)) .> i) .> j == f' .> (g' .> h) .> i .> j.
Proof.
  mor'.
Restart.
  wuut.
Abort.

Goal
  forall (C : Cat) (X Y Z W V T: Ob C) (f f' : Hom X Y) (g g' : Hom Y Z)
    (h : Hom Z W) (i : Hom W V) (j : Hom V T),
      f == f .> id _ .> id _.
Proof.
  mor'. reflexivity.
Qed.

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
Qed.*)