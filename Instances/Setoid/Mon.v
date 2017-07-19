Add Rec LoadPath "/home/zeimer/Code/Coq".

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

Definition MonHom (X Y : Mon) : Type :=
    {f : SgrHom X Y | f neutr == neutr}.

Definition MonHom_SgrHom (X Y : Mon) (f : MonHom X Y)
    : SgrHom X Y := proj1_sig f.
Coercion MonHom_SgrHom : MonHom >-> SgrHom.

Inductive exp (X : Mon) : Type :=
    | Id : exp X
    | Var : X -> exp X
    | Op : exp X -> exp X -> exp X
    | Mor : forall A : Mon, MonHom A X -> exp A -> exp X.

Arguments Id [X].
Arguments Var [X] _.
Arguments Op [X] _ _.
Arguments Mor [X A] _ _ .

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
    destruct (simplify e1), (simplify e2); simpl in *; try
    rewrite <- IHe1, <- IHe2; try rewrite neutr_l; try rewrite neutr_r;
    try reflexivity.
    destruct (simplify e); cbn in *; rewrite <- IHe.
      destruct m; cbn in *. symmetry. assumption.
      reflexivity.
      destruct m, x; cbn in *. rewrite e1. reflexivity.
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
  induction l1 as [| h1 t1]; simpl; intros.
    rewrite neutr_l. reflexivity.
    rewrite <- assoc, IHt1. reflexivity.
Qed.

Lemma expDenoteL_hom :
  forall (X Y : Mon) (f : MonHom X Y) (l : list X),
    expDenoteL (map f l) == f (expDenoteL l).
Proof.
  induction l as [| h t]; simpl.
    destruct f; simpl in *. symmetry. assumption.
    destruct f, x; simpl in *. rewrite e0, IHt. reflexivity.
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

Ltac reify e :=
lazymatch e with
    | @neutr ?X => constr:(@Id X)
    | op ?e1 ?e2 =>
        let e1' := reify e1 in
        let e2' := reify e2 in constr:(Op e1' e2')
    | SetoidHom_Fun (SgrHom_Fun (MonHom_SgrHom ?f)) ?e =>
        let e' := reify e in constr:(Mor f e')
    | ?v => constr:(Var v)
end.

Ltac reflect_mon := simpl; intros;
match goal with
    | |- ?e1 == ?e2 =>
        let e1' := reify e1 in
        let e2' := reify e2 in
          change (expDenote e1' == expDenote e2');
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

Instance MonHomSetoid (X Y : Mon) : Setoid (MonHom X Y) :=
{
    equiv := fun f g : MonHom X Y =>
      @equiv _ (SgrHomSetoid X Y) (proj1_sig f) (proj1_sig g)
}.
Proof. apply Setoid_kernel_equiv. Defined.

Definition MonComp (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z)
    : MonHom X Z.
Proof.
  red. exists (SgrComp f g). mon.
Defined.

Definition MonId (X : Mon) : MonHom X X.
Proof.
  red. exists (SgrId X). mon.
Defined.

Instance MonCat : Cat :=
{
    Ob := Mon;
    Hom := MonHom;
    HomSetoid := MonHomSetoid;
    comp := MonComp;
    id := MonId
}.
Proof. all: mon. Defined.

Instance Mon_init : Mon :=
{
    sgr := Sgr_term;
    neutr := tt
}.
Proof. all: mon. Defined.

Definition Mon_Setoid_create (X : Mon) : SetoidHom Mon_init X.
Proof.
  red. exists (fun _ => neutr). mon.
Defined.

Definition Mon_Sgr_create (X : Mon) : SgrHom Mon_init X.
Proof.
  red. exists (Mon_Setoid_create X). mon.
Defined.

Definition Mon_create (X : Mon) : Hom Mon_init X.
Proof.
  do 3 red. exists (Mon_Sgr_create X). mon.
Defined.

Instance Mon_has_init : has_init MonCat :=
{
    init := Mon_init;
    create := Mon_create
}.
Proof. mon. Defined.

Instance Mon_term : Mon :=
{
    sgr := Sgr_term;
    neutr := tt
}.
Proof. all: mon. Defined.

Definition Mon_Setoid_delete (X : Mon) : SetoidHom X Mon_term.
Proof.
  red. exists (fun _ => tt). mon.
Defined.

Definition Mon_Sgr_delete (X : Mon) : SgrHom X Mon_term.
Proof.
  red. exists (Mon_Setoid_delete X). mon.
Defined.

Definition Mon_delete (X : Mon) : Hom X Mon_term.
Proof.
  do 3 red. exists (Mon_Sgr_delete X). mon.
Defined.

Instance Mon_has_term : has_term MonCat :=
{
    term := Mon_term;
    delete := Mon_delete
}.
Proof. mon. Defined.

Instance Mon_has_zero : has_zero MonCat :=
{
    zero_is_initial := Mon_has_init;
    zero_is_terminal := Mon_has_term
}.
Proof. mon. Defined.

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
  red. exists (Sgr_fpair f g). (* TODO : make faster *) Time mon.
Defined.

Instance Mon_has_products : has_products MonCat :=
{
    prodOb := Mon_prodOb;
    proj1 := Mon_proj1;
    proj2 := Mon_proj2;
    fpair := Mon_fpair
}.
Proof.
  proper.
  repeat split; mon.
Defined.

Instance forgetful : Functor MonCat CoqSetoid :=
{
    fob := fun X : Mon => @setoid (sgr X);
}.
Proof.
  destruct 1. destruct x. exact x.
  proper. all: mon.
Time Defined.

Notation "'U'" := forgetful.

Definition free_monoid
  (X : Ob CoqSetoid) (M : Mon) (p : Hom X (fob U M)) : Prop :=
    forall (N : Mon) (q : SetoidHom X (fob U N)),
      exists!! h : MonHom M N, q == p .> fmap U h.
Print Setoid'.
Require Import Arith.

Instance MonListUnit_Setoid' : Setoid' :=
{
    carrier := nat;
    (*setoid := {| equiv := fun n m => beq_nat n m = true |}*)
    setoid := {| equiv := eq |}
}.
(*Proof.
  split; red; intro.
    erewrite beq_nat_refl. auto.
    induction x as [| x']; destruct y; simpl; auto.
    induction x as [| x']; destruct y; simpl; auto.
      inversion 1.
      inversion 1.
      destruct z.
        inversion 2.
        intros. eapply IHx'; eauto.
Defined.*)

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
  all: simpl; intros.
    rewrite plus_assoc_reverse. trivial.
    trivial.
    rewrite plus_n_O. trivial.
Defined.

Definition MonListUnit_p : SetoidHom CoqSetoid_term MonListUnit.
Proof.
  red; simpl. exists (fun _ => 1). proper.
Defined.

Theorem free_monoid_MonListUnit :
  @free_monoid CoqSetoid_term MonListUnit MonListUnit_p.
Proof.
  unfold free_monoid. intros.
  Definition f1 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : SetoidHom MonListUnit N.
    red. exists (fix f (n : nat) : N :=
      match n with
          | 0 => @neutr N
          | S n' => op (q tt) (f n')
      end).
    proper. subst. reflexivity.
  Defined.
  Definition f2 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : SgrHom MonListUnit N.
    red. exists (f1 N q). induction x as [| x']. simpl.
      mon.
      simpl. intro. rewrite <- assoc, IHx'. reflexivity.
  Defined.
  Definition f3 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : MonHom MonListUnit N.
    red. exists (f2 N q). mon.
  Defined.
  exists (f3 N q). repeat split.
    simpl. destruct x. mon.
    destruct y, x; simpl in *; intros ? n. induction n as [| n'].
      mon.
      pose (H' := e0). specialize (H' n' 1). rewrite plus_comm in H'.
        rewrite H'. rewrite e0 in H'. rewrite <- H'. f_equiv; mon.
Defined.