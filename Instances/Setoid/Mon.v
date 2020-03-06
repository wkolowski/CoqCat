Require Export Cat.
Require Import Cat.Limits.InitTerm.
Require Import Cat.Limits.BinProdCoprod.

Require Export Cat.Instances.Setoid.Sgr.

Set Implicit Arguments.

Class Mon : Type :=
{
    sgr :> Sgr;
    neutr : sgr;
    neutr_l : forall a : sgr, op neutr a = a;
    neutr_r : forall a : sgr, op a neutr = a
}.

Arguments sgr _ : clear implicits.

Coercion sgr : Mon >-> Sgr.

Hint Resolve neutr_l neutr_r.

Class MonHom (X Y : Mon) : Type :=
{
    sgrHom :> SgrHom X Y;
    pres_neutr : sgrHom neutr == neutr;
}.

Coercion sgrHom : MonHom >-> SgrHom.

Inductive exp (X : Mon) : Type :=
    | Id : exp X
    | Var : X -> exp X
    | Op : exp X -> exp X -> exp X
    | Mor : forall A : Mon, MonHom A X -> exp A -> exp X.

Arguments Id {X}.
Arguments Var {X} _.
Arguments Op {X} _ _.
Arguments Mor {X A} _ _ .

Fixpoint expDenote {X : Mon} (e : exp X) : X :=
match e with
    | Id => neutr
    | Var v => v
    | Op e1 e2 => op (expDenote e1) (expDenote e2)
    | Mor f e' => f (expDenote e')
end.

Require Import List.
Import ListNotations.

Fixpoint simplify {X : Mon} (e : exp X) : exp X :=
match e with
    | Id => Id
    | Var v => Var v
    | Op e1 e2 =>
        match simplify e1, simplify e2 with
            | Id, e2' => e2'
            | e1', Id => e1'
            | e1', e2' => Op e1' e2'
        end
    | Mor f e' => match simplify e' with
        | Id => Id
        | Op e1 e2 => Op (Mor f e1) (Mor f e2)
        | e'' => Mor f e''
    end
end.

Theorem simplify_correct :
  forall (X : Mon) (e : exp X),
    expDenote (simplify e) == expDenote e.
Proof.
  induction e; cbn.
    reflexivity.
    reflexivity.
    destruct (simplify e1), (simplify e2); cbn in *;
      rewrite <- ?IHe1, <- ?IHe2, ?neutr_l, ?neutr_r; try reflexivity.
    destruct (simplify e); cbn in *; rewrite <- IHe.
      rewrite pres_neutr. reflexivity.
      reflexivity.
      rewrite pres_op. reflexivity.
      rewrite IHe. reflexivity.
Qed.

Fixpoint expDenoteL {X : Mon} (l : list X) : X :=
match l with
    | [] => neutr
    | h :: t => op h (expDenoteL t)
end.

Lemma expDenoteL_app :
  forall (X : Mon) (l1 l2 : list X),
    expDenoteL (l1 ++ l2) == op (expDenoteL l1) (expDenoteL l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    rewrite neutr_l. reflexivity.
    rewrite <- assoc, IHt1. reflexivity.
Qed.

Lemma expDenoteL_hom :
  forall (X Y : Mon) (f : MonHom X Y) (l : list X),
    expDenoteL (map f l) == f (expDenoteL l).
Proof.
  induction l as [| h t]; simpl.
    rewrite pres_neutr. reflexivity.
    rewrite pres_op, IHt. reflexivity.
Qed.

Fixpoint flatten {X : Mon} (e : exp X) : list X :=
match e with
    | Id => []
    | Var v => [v]
    | Op e1 e2 => flatten e1 ++ flatten e2
    | Mor f e' => map f (flatten e')
end.

Theorem flatten_correct :
  forall (X : Mon) (e : exp X),
    expDenoteL (flatten e) == expDenote e.
Proof.
  induction e; simpl.
    reflexivity.
    rewrite neutr_r. reflexivity.
    rewrite expDenoteL_app. rewrite IHe1, IHe2. reflexivity.
    rewrite expDenoteL_hom. rewrite IHe. reflexivity.
Qed.

Theorem mon_reflect :
  forall (X : Mon) (e1 e2 : exp X),
    expDenoteL (flatten (simplify e1)) ==
    expDenoteL (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  intros. rewrite !flatten_correct, !simplify_correct in H. assumption.
Qed.

Class Reify (X : Mon) (x : X) : Type :=
{
    reify : exp X;
    reify_spec : expDenote reify == x
}.

Arguments Reify {X} _.
Arguments reify {X} _ {Reify}.

#[refine]
Instance ReifyVar (X : Mon) (x : X) : Reify x | 1 :=
{
    reify := Var x
}.
Proof. reflexivity. Defined.

#[refine]
Instance ReifyOp (X : Mon) (a b : X) (Ra : Reify a) (Rb : Reify b)
    : Reify (@op X a b) | 0 :=
{
    reify := Op (reify a) (reify b)
}.
Proof.
  cbn. rewrite !reify_spec. reflexivity.
Defined.

#[refine]
Instance ReifyHom (X Y : Mon) (f : MonHom X Y) (x : X) (Rx : Reify x)
    : Reify (f x) | 0 :=
{
    reify := Mor f (reify x)
}.
Proof.
  cbn. rewrite reify_spec. reflexivity.
Defined.

#[refine]
Instance ReifyId (X : Mon) : Reify neutr | 0 :=
{
    reify := Id
}.
Proof.
  cbn. reflexivity.
Defined.

Ltac reflect_mon := simpl; intros;
match goal with
    | |- ?e1 == ?e2 =>
        change (expDenote (reify e1) == expDenote (reify e2));
        apply mon_reflect; simpl
end.

Ltac mon_simpl := sgr_simpl.

Ltac monob M := try intros until M;
match type of M with
  | Mon =>
    let a := fresh M "_neutr" in
    let b := fresh M "_neutr_l" in
    let c := fresh M "_neutr_r" in
      destruct M as [?M a b c]
  | Ob _ => progress simpl in M; monob M
end; simpl.

Ltac monob' M := monob M; sgrob M.

Ltac monobs_template tac := repeat
match goal with
  | M : Mon |- _ => tac M
  | M : Ob _ |- _ => tac M
end.

Ltac monobs := monobs_template monob.
Ltac monobs' := monobs_template monob'.

Ltac monhom f := try intros until f;
match type of f with
    | MonHom _ _ =>
      let a := fresh f "_pres_neutr" in destruct f as [f a]
    | Hom _ _ => progress simpl in f; monhom f
end.

Ltac monhom' f := monhom f; sgrhom f.

Ltac monhoms_template tac := intros; repeat
match goal with
  | f : MonHom _ _ |- _ => tac f
  | f : Hom _ _ |- _ => tac f
end; mon_simpl.

Ltac monhoms := monhoms_template monhom.
Ltac monhoms' := monhoms_template monhom'.

Ltac mon := intros; try (reflect_mon; try reflexivity; fail); repeat
match goal with
    | |- _ == _ => reflect_mon; reflexivity
    | |- Equivalence _ => solve_equiv
    | |- Proper _ _ => proper
    | |- (_, _) = (_, _) => f_equal
    | _ => mon_simpl || monobs' || monhoms' || cat
end.

Goal forall (X : Mon) (a b c : X),
  op a (op b c) == op (op a b) c.
Proof.
  reflect_mon. reflexivity.
Qed.

Goal forall (X : Mon) (f : MonHom X X) (a b : X),
  f (op a b) == op (f a) (f b).
Proof.
  reflect_mon. reflexivity.
Qed.

Goal forall (X : Mon) (f : MonHom X X) (a b c : X),
  op (f (f neutr)) (op (f a) (f (op b c))) ==
  op (f a) (op (f b) (f c)).
Proof.
  reflect_mon. reflexivity.
Qed.

Goal forall (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z),
  g (f neutr) == neutr.
Proof.
  reflect_mon. reflexivity.
Qed.

(* TODO : improve reflection *)
Theorem flat_reflect_goal :
  forall (X : Mon) (e1 e2 : exp X),
    flatten (simplify e1) = flatten (simplify e2) ->
      expDenote e1 == expDenote e2.
Proof.
  intros. apply mon_reflect. rewrite H. reflexivity.
Qed.

Theorem flat_reflect_hyp :
  forall (X : Mon) (e1 e2 : exp X),
    expDenote e1 == expDenote e2 ->
      flatten (simplify e1) = flatten (simplify e2).
Proof.
  induction e1. destruct e2; cbn; intros; auto.
    Focus 2.
Admitted.

Theorem flat_reflect_hyp' :
  forall (X : Mon) (e1 e2 : exp X),
    expDenote e1 == expDenote e2 ->
      expDenoteL (flatten (simplify e1)) == expDenoteL (flatten (simplify e2)).
Proof.
  intros. rewrite !flatten_correct, !simplify_correct. assumption.
Qed.

Ltac reflect_goal := simpl; intros;
match goal with
    | |- ?e1 == ?e2 =>
        change (expDenote (reify e1) == expDenote (reify e2));
          apply flat_reflect_goal
end.

Theorem cons_nil_all :
  forall (A : Type) (h h' : A),
    [h] = [h'] -> forall l : list A, cons h l = cons h' l.
Proof.
  inversion 1. subst. auto.
Qed.

Goal forall (X : Mon) (a b b' c : X),
  b == b' -> op a (op b c) == op (op a b') c.
Proof.
  intros. reflect_goal. cbn.
  match goal with
      | H : ?x == ?y |- _ =>
          change (expDenote (reify x) == expDenote (reify y)) in H;
            apply flat_reflect_hyp in H; cbn in H
  end.
  assert (forall l, cons b l = cons b' l). apply cons_nil_all. auto.
  assert (exists l1 l2, [a; b'; c] = l1 ++ [b] ++ l2).
    do 2 eexists. eauto.
Abort.

#[refine]
Instance MonHomSetoid (X Y : Mon) : Setoid (MonHom X Y) :=
{
    equiv := fun f g : MonHom X Y =>
      @equiv _ (SgrHomSetoid X Y) f g
}.
Proof. apply Setoid_kernel_equiv. Defined.

Definition MonComp (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z)
    : MonHom X Z.
Proof.
  exists (SgrComp f g). mon.
Defined.

Definition MonId (X : Mon) : MonHom X X.
Proof.
  exists (SgrId X). mon.
Defined.

#[refine]
Instance MonCat : Cat :=
{
    Ob := Mon;
    Hom := MonHom;
    HomSetoid := MonHomSetoid;
    comp := MonComp;
    id := MonId
}.
Proof. all: mon. Defined.

#[refine]
Instance Mon_init : Mon :=
{
    sgr := Sgr_term;
    neutr := tt
}.
Proof. all: mon. Defined.

Definition Mon_Setoid_create (X : Mon) : SetoidHom Mon_init X.
Proof.
  exists (fun _ => neutr). mon.
Defined.

Definition Mon_Sgr_create (X : Mon) : SgrHom Mon_init X.
Proof.
  exists (Mon_Setoid_create X). mon.
Defined.

Definition Mon_create (X : Mon) : Hom Mon_init X.
Proof.
  exists (Mon_Sgr_create X). mon.
Defined.

#[refine]
Instance Mon_has_init : has_init MonCat :=
{
    init := Mon_init;
    create := Mon_create
}.
Proof. mon. Defined.

#[refine]
Instance Mon_term : Mon :=
{
    sgr := Sgr_term;
    neutr := tt
}.
Proof. all: mon. Defined.

Definition Mon_Setoid_delete (X : Mon) : SetoidHom X Mon_term.
Proof.
  exists (fun _ => tt). mon.
Defined.

Definition Mon_Sgr_delete (X : Mon) : SgrHom X Mon_term.
Proof.
  exists (Mon_Setoid_delete X). mon.
Defined.

Definition Mon_delete (X : Mon) : Hom X Mon_term.
Proof.
  exists (Mon_Sgr_delete X). mon.
Defined.

#[refine]
Instance Mon_has_term : has_term MonCat :=
{
    term := Mon_term;
    delete := Mon_delete
}.
Proof. mon. Defined.

#[refine]
Instance Mon_has_zero : has_zero MonCat :=
{
    zero_is_initial := Mon_has_init;
    zero_is_terminal := Mon_has_term
}.
Proof. mon. Defined.

#[refine]
Instance Mon_prodOb (X Y : Mon) : Mon :=
{
    sgr := Sgr_prodOb X Y;
    neutr := (neutr, neutr);
}.
Proof. all: destruct a; mon. Defined.

Definition Mon_proj1 (X Y : Mon) : Hom (Mon_prodOb X Y) X.
Proof.
  mon_simpl. exists (Sgr_proj1 X Y). mon.
Defined.

Definition Mon_proj2 (X Y : Mon) : Hom (Mon_prodOb X Y) Y.
Proof.
  mon_simpl. exists (Sgr_proj2 X Y). mon.
Defined.

Definition Mon_fpair (A B X : Mon) (f : MonHom X A) (g : MonHom X B)
    : MonHom X (Mon_prodOb A B).
Proof.
  exists (Sgr_fpair f g). mon.
Defined.

#[refine]
Instance Mon_has_products : has_products MonCat :=
{
    prodOb := Mon_prodOb;
    proj1 := Mon_proj1;
    proj2 := Mon_proj2;
    fpair := Mon_fpair
}.
Proof.
  proper.
  repeat split; cat. (* TODO : mon doesn't work *)
Defined.

#[refine]
Instance forgetful : Functor MonCat CoqSetoid :=
{
    fob := fun X : Mon => @setoid (sgr X);
}.
Proof.
  cbn. intros. exact X.
  proper. all: mon.
Time Defined.

Notation "'U'" := forgetful.

Definition free_monoid
  (X : Ob CoqSetoid) (M : Mon) (p : Hom X (fob U M)) : Prop :=
    forall (N : Mon) (q : SetoidHom X (fob U N)),
      exists!! h : MonHom M N, q == p .> fmap U h.

Require Import Arith.

Instance MonListUnit_Setoid' : Setoid' :=
{
    carrier := nat;
    setoid := {| equiv := eq |}
}.

#[refine]
Instance MonListUnit : Mon :=
{
    sgr :=
    {|
        setoid := MonListUnit_Setoid';
        op := plus
    |};
    neutr := 0
}.
Proof.
  all: simpl; intros; ring.
Defined.

Definition MonListUnit_p : SetoidHom CoqSetoid_term MonListUnit.
Proof.
  cbn. exists (fun _ => 1). proper.
Defined.

(*From mathcomp Require Import ssreflect.*)

Set Nested Proofs Allowed.

Theorem free_monoid_MonListUnit :
  @free_monoid CoqSetoid_term MonListUnit MonListUnit_p.
Proof.
  unfold free_monoid. intros.
  (*pose f1 : SetoidHom MonListUnit N :=
  {|
      func := fix f n : N :=
      match n with
          | 0 => @neutr N
          | S n' => op (q tt) (f n')
      end;
      func_Proper := ltac: (proper; subst; reflexivity)
  |}.
  pose f2 : SgrHom MonListUnit N :=
  {|
      setoidHom := @f1;
      pres_op := ltac:(mon)
  |}.*)
  Definition f1 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : SetoidHom MonListUnit N.
    exists (fix f (n : nat) : N :=
      match n with
          | 0 => @neutr N
          | S n' => op (q tt) (f n')
      end).
    proper. subst. reflexivity.
  Defined.
  Definition f2 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : SgrHom MonListUnit N.
    exists (f1 N q). induction x as [| x']. simpl.
      mon.
      simpl. intro. rewrite <- assoc. rewrite -> IHx'. reflexivity.
  Defined.
  Definition f3 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : MonHom MonListUnit N.
    exists (f2 N q). mon.
  Defined.
  exists (f3 N q). repeat split.
    simpl. destruct x. mon.
    destruct y, sgrHom0; simpl in *; intros ? n. induction n as [| n'].
      mon.
      pose (H' := pres_op). specialize (H' n' 1). rewrite plus_comm in H'.
        rewrite H'. rewrite -> pres_op in H'. rewrite <- H', IHn'. f_equiv; mon.
Defined.