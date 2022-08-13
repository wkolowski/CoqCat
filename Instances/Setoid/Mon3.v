From Cat Require Export Cat.
From Cat.Limits Require Import InitTerm Product Coproduct.
From Cat Require Export Instances.Setoid.Sgr3.

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

#[global] Hint Resolve neutr_l neutr_r : core.

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

Arguments Id  {X}.
Arguments Var {X} _.
Arguments Op  {X} _ _.
Arguments Mor {X A} _ _ .

Fixpoint expDenote {X : Mon} (e : exp X) : X :=
match e with
| Id => neutr
| Var v => v
| Op e1 e2 => op (expDenote e1) (expDenote e2)
| Mor f e' => f (expDenote e')
end.

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
| Mor f e' =>
  match simplify e' with
  | Id => Id
  | Op e1 e2 => Op (Mor f e1) (Mor f e2)
  | e'' => Mor f e''
  end
end.

Lemma simplify_correct :
  forall (X : Mon) (e : exp X),
    expDenote (simplify e) == expDenote e.
Proof.
  induction e; cbn.
    reflexivity.
    reflexivity.
    destruct (simplify e1), (simplify e2); cbn in *;
      rewrite <- ?IHe1, <- ?IHe2, ?neutr_l, ?neutr_r; reflexivity.
    destruct (simplify e); cbn in *; rewrite <- IHe.
      rewrite pres_neutr. reflexivity.
      reflexivity.
      rewrite pres_op. reflexivity.
      reflexivity.
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
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite neutr_l. reflexivity.
    rewrite <- assoc, IHt1. reflexivity.
Qed.

Lemma expDenoteL_hom :
  forall (X Y : Mon) (f : MonHom X Y) (l : list X),
    expDenoteL (map f l) == f (expDenoteL l).
Proof.
  induction l as [| h t]; cbn.
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

Lemma flatten_correct :
  forall (X : Mon) (e : exp X),
    expDenoteL (flatten e) == expDenote e.
Proof.
  induction e; cbn.
    reflexivity.
    rewrite neutr_r. reflexivity.
    rewrite expDenoteL_app, IHe1, IHe2. reflexivity.
    rewrite expDenoteL_hom, IHe. reflexivity.
Qed.

Lemma mon_reflect :
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
#[export]
Instance ReifyVar (X : Mon) (x : X) : Reify x | 1 :=
{
  reify := Var x
}.
Proof. reflexivity. Defined.

#[refine]
#[export]
Instance ReifyOp (X : Mon) (a b : X) (Ra : Reify a) (Rb : Reify b) : Reify (@op X a b) | 0 :=
{
  reify := Op (reify a) (reify b)
}.
Proof.
  cbn. rewrite !reify_spec. reflexivity.
Defined.

#[refine]
#[export]
Instance ReifyHom (X Y : Mon) (f : MonHom X Y) (x : X) (Rx : Reify x) : Reify (f x) | 0 :=
{
  reify := Mor f (reify x)
}.
Proof.
  cbn. rewrite !reify_spec. reflexivity.
Defined.

#[refine]
#[export]
Instance ReifyId (X : Mon) : Reify neutr | 0 :=
{
  reify := Id
}.
Proof.
  cbn. reflexivity.
Defined.

Ltac reflect_mon := cbn; intros;
match goal with
| |- ?e1 == ?e2 =>
  change (expDenote (reify e1) == expDenote (reify e2));
  apply mon_reflect; cbn
end.

Ltac mon_simpl := sgr_simpl.

Ltac monob M := try intros until M;
match type of M with
| Mon =>
  let a := fresh M "_neutr" in
  let b := fresh M "_neutr_l" in
  let c := fresh M "_neutr_r" in
    destruct M as [?M a b c]
| Ob _ => progress cbn in M; monob M
end; cbn.

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
| Hom _ _ => progress cbn in f; monhom f
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

Goal
  forall (X : Mon) (a b c : X),
    op a (op b c) == op (op a b) c.
Proof.
  reflect_mon. reflexivity.
Qed.

Goal
  forall (X : Mon) (f : MonHom X X) (a b : X),
    f (op a b) == op (f a) (f b).
Proof.
  reflect_mon. reflexivity.
Qed.

Goal
  forall (X : Mon) (f : MonHom X X) (a b c : X),
    op (f (f neutr)) (op (f a) (f (op b c))) == op (f a) (op (f b) (f c)).
Proof.
  reflect_mon. reflexivity.
Qed.

Goal
  forall (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z),
    g (f neutr) == neutr.
Proof.
  reflect_mon. reflexivity.
Qed.

#[refine]
#[export]
Instance MonHomSetoid (X Y : Mon) : Setoid (MonHom X Y) :=
{
  equiv := fun f g : MonHom X Y => @equiv _ (SgrHomSetoid X Y) f g
}.
Proof. apply Setoid_kernel_equiv. Defined.

Definition MonComp (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z) : MonHom X Z.
Proof.
  exists (SgrComp f g). mon.
Defined.

Definition MonId (X : Mon) : MonHom X X.
Proof.
  exists (SgrId X). mon.
Defined.

#[refine]
#[export]
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
#[export]
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
#[export]
Instance HasInit_Mon : HasInit MonCat :=
{
  init := Mon_init;
  create := Mon_create
}.
Proof. mon. Defined.

#[refine]
#[export]
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
#[export]
Instance HasTerm_Mon : HasTerm MonCat :=
{
  term := Mon_term;
  delete := Mon_delete
}.
Proof. mon. Defined.

#[refine]
#[export]
Instance HasZero_Mon : HasZero MonCat :=
{
  HasZero_HasInit := HasInit_Mon;
  HasZero_HasTerm := HasTerm_Mon
}.
Proof. mon. Defined.

#[refine]
#[export]
Instance Mon_prodOb (X Y : Mon) : Mon :=
{
  sgr := Sgr_prodOb X Y;
  neutr := (neutr, neutr);
}.
Proof. all: destruct a; mon. Defined.

Definition Mon_outl (X Y : Mon) : Hom (Mon_prodOb X Y) X.
Proof.
  mon_simpl. exists (Sgr_outl X Y). mon.
Defined.

Definition Mon_outr (X Y : Mon) : Hom (Mon_prodOb X Y) Y.
Proof.
  mon_simpl. exists (Sgr_outr X Y). mon.
Defined.

Definition Mon_fpair (A B X : Mon) (f : MonHom X A) (g : MonHom X B) : MonHom X (Mon_prodOb A B).
Proof.
  exists (Sgr_fpair f g). mon.
Defined.

#[refine]
#[export]
Instance HasProducts_Mon : HasProducts MonCat :=
{
  prodOb := Mon_prodOb;
  outl := Mon_outl;
  outr := Mon_outr;
  fpair := Mon_fpair
}.
Proof.
  proper.
  repeat split; cat. (* TODO : mon doesn't work *)
Defined.

#[refine]
#[export]
Instance forgetful : Functor MonCat CoqSetoid :=
{
  fob := fun X : Mon => @setoid (sgr X);
}.
Proof.
  cbn. intros. exact X.
  proper. all: mon.
Defined.

Notation "'U'" := forgetful.

Definition free_monoid
  (X : Ob CoqSetoid) (M : Mon) (p : Hom X (fob U M)) : Prop :=
    forall (N : Mon) (q : SetoidHom X (fob U N)),
      exists!! h : MonHom M N, q == p .> fmap U h.

#[export]
Instance MonListUnit_Setoid' : Setoid' :=
{
  carrier := nat;
  setoid := {| equiv := eq |}
}.

#[refine]
#[export]
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
  all: cbn; intros; ring.
Defined.

Definition MonListUnit_p : SetoidHom CoqSetoid_term MonListUnit.
Proof.
  cbn. exists (fun _ => 1). proper.
Defined.

Set Nested Proofs Allowed.

Lemma free_monoid_MonListUnit :
  @free_monoid CoqSetoid_term MonListUnit MonListUnit_p.
Proof.
  unfold free_monoid. intros.
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
      simpl. intro. rewrite <- assoc, IHx'. reflexivity.
  Defined.
  Definition f3 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : MonHom MonListUnit N.
    exists (f2 N q). mon.
  Defined.
  exists (f3 N q). repeat split.
    simpl. destruct x. mon.
    destruct y, sgrHom0; cbn in *; intros ? n. induction n as [| n'].
      mon.
      pose (H' := pres_op). specialize (H' n' 1). rewrite plus_comm in H'.
        rewrite H'. rewrite pres_op in H'. rewrite <- H'. f_equiv; mon.
Defined.