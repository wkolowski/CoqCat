From CoqAlgs.Sorting Require Import Perm InsertionSort.

From Cat Require Export Cat.
From Cat.Limits Require Import Initial Terminal Product Coproduct.
From Cat Require Export Instances.Setoid.Mon.

Set Implicit Arguments.

Class ComMon : Type :=
{
  mon :> Mon;
  com : forall x y : mon, op x y == op y x
}.

Arguments mon _ : clear implicits.

Coercion mon : ComMon >-> Mon.

Inductive exp (X : ComMon) : Type :=
| Id : exp X
| Var : nat -> exp X
| Op : exp X -> exp X -> exp X
| Mor : forall A : ComMon, MonHom A X -> exp A -> exp X.

Arguments Id {X}.
Arguments Var {X} _.
Arguments Op {X} _ _.
Arguments Mor {X A} _ _.

Fixpoint expDenote {X : ComMon} (env : nat -> X) (e : exp X) : X :=
match e with
| Id => neutr
| Var n => env n
| Op e1 e2 => op (expDenote env e1) (expDenote env e2)
| Mor _ _ => neutr
end.

Fixpoint simplifyExp {X : ComMon} (e : exp X) : exp X :=
match e with
| Id => Id
| Var v => Var v
| Op e1 e2 =>
  match simplifyExp e1, simplifyExp e2 with
  | Id, e2' => e2'
  | e1', Id => e1'
  | e1', e2' => Op e1' e2'
  end
| Mor f e' =>
  match simplifyExp e' with
  | Id => Id
  | Op e1 e2 => Op (Mor f e1) (Mor f e2)
  | e'' => Mor f e''
  end
end.

Lemma simplifyExp_correct :
  forall (X : ComMon) (env : nat -> X) (e : exp X),
    expDenote env (simplifyExp e) == expDenote env e.
Proof.
  induction e; cbn.
    easy.
    easy.
    now destruct (simplifyExp e1), (simplifyExp e2); cbn in *;
      rewrite <- ?IHe1, <- ?IHe2, ?neutr_l, ?neutr_r.
    now destruct (simplifyExp e); cbn in *; rewrite ?neutr_l.
Qed.

Fixpoint expDenoteL {X : ComMon} (env : nat -> X) (l : list nat) : X :=
match l with
| [] => neutr
| h :: t => op (env h) (expDenoteL env t)
end.

Lemma expDenoteL_app :
  forall (X : ComMon) (env : nat -> X) (l1 l2 : list nat),
    expDenoteL env (l1 ++ l2) == op (expDenoteL env l1) (expDenoteL env l2).
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    now rewrite neutr_l.
    now rewrite <- assoc, IHt1.
Qed.

Fixpoint flatten {X : ComMon} (e : exp X) : list nat :=
match e with
| Id => []
| Var v => [v]
| Op e1 e2 => flatten e1 ++ flatten e2
| Mor f e' => []
end.

Lemma flatten_correct :
  forall (X : ComMon) (env : nat -> X) (e : exp X),
    expDenoteL env (flatten e) == expDenote env e.
Proof.
  induction e; cbn.
    easy.
    now rewrite neutr_r.
    now rewrite expDenoteL_app, IHe1, IHe2.
    now rewrite ?expDenoteL_hom, ?IHe.
Qed.

Lemma expDenoteL_Permutation :
  forall (X : ComMon) (env : nat -> X) (l1 l2 : list nat),
    Permutation l1 l2 -> expDenoteL env l1 == expDenoteL env l2.
Proof.
  induction 1; cbn.
    easy.
    now rewrite IHPermutation.
    now rewrite !assoc, (com (env y)).
    now rewrite IHPermutation1, IHPermutation2.
Qed.

(* TOOD: fix *) Lemma sort_correct :
  forall (X : ComMon) (env : nat -> X) (l : list nat) (s : Sort le),
    expDenoteL env (s l) == expDenoteL env l.
Proof.
(*
  intros. apply expDenoteL_Permutation. apply (perm_Permutation).
  now rewrite <- sort_perm.
Qed.
*)
Admitted.

(* TODO: uncomment code on commutative monoid simplification *)
(*
Definition simplify {X : ComMon} (e : exp X) : list nat :=
  insertionSort le (flatten (simplifyExp e)).

Lemma simplify_correct :
  forall (X : ComMon) (env : nat -> X) (e1 e2 : exp X),
    expDenoteL env (simplify e1) == expDenoteL env (simplify e2) ->
      expDenote env e1 == expDenote env e2.
Proof.
  unfold simplify. intros.
  rewrite (@sort_correct X env (flatten (simplifyExp e1))
                         (Sort_insertionSort natle)),
          (@sort_correct X env (flatten (simplifyExp e2))
                         (Sort_insertionSort natle))
  in H.
  now rewrite !flatten_correct, !simplifyExp_correct in H.
Qed.

Ltac inList x l :=
match l with
| [] => false
| x :: _ => true
| _ :: ?l' => inList x l'
end.

Ltac addToList x l :=
  let b := inList x l in
match b with
| true => l
| false => constr:(x :: l)
end.

Ltac lookup x l :=
match l with
| x :: _ => constr:(0)
| _ :: ?l' => let n := lookup x l' in constr:(S n)
end.

Ltac allVars xs e :=
match e with
| op ?e1 ?e2 => let xs' := allVars xs e2 in allVars xs' e1
| ?f ?e' => allVars xs e'
| _ => addToList e xs
end.

Ltac reifyTerm env x :=
match x with
| neutr => constr:(Id)
| op ?a ?b =>
  let e1 := reifyTerm env a in
  let e2 := reifyTerm env b in constr:(Op e1 e2)
| _ => let n := lookup x env in constr:(Var n)
end.

Ltac functionalize l X :=
let rec loop n l' :=
  match l' with
  | [] => constr:(fun _ : nat => @neutr X)
  | ?h :: ?t =>
    let f := loop (S n) t in
    constr:(fun m : nat => if m =? n then h else f m)
  end
in loop 0 l.

Ltac reify X :=
match goal with
| |- ?e1 == ?e2 =>
  let xs := allVars constr:(@nil X) e1 in
  let xs' := allVars xs e2 in
  let r1 := reifyTerm xs' e1 in
  let r2 := reifyTerm xs' e2 in
  let env := functionalize xs' X in
    change (expDenote env r1 == expDenote env r2)
end.

Ltac reifyEqv X env a b :=
  let e1 := reifyTerm env a in
  let e2 := reifyTerm env b in constr:((e1, e2)).

(* TODO : improve reflection *)
Lemma flat_reflect_goal :
  forall (X : ComMon) (env : nat -> X) (e1 e2 : exp X),
    flatten (simplifyExp e1) = flatten (simplifyExp e2) ->
      expDenote env e1 == expDenote env e2.
Proof.
  intros. apply simplify_correct. unfold simplify. now rewrite H.
Qed.

Lemma flat_reflect_hyp :
  forall (X : ComMon) (env : nat -> X) (e1 e2 : exp X),
    expDenote env e1 == expDenote env e2 ->
      flatten (simplifyExp e1) == flatten (simplifyExp e2).
Proof.
  now induction e1; destruct e2; cbn; intros.
Qed.

Lemma flat_reflect_hyp' :
  forall (X : ComMon) (env : nat -> X) (e1 e2 : exp X) (s : Sort natle),
    expDenote env e1 == expDenote env e2 ->
      expDenoteL env (s (flatten (simplifyExp e1))) ==
      expDenoteL env (s (flatten (simplifyExp e2))).
Proof.
  now intros; rewrite !sort_correct, !flatten_correct, !simplifyExp_correct.
Qed.

Ltac cmon_subst := repeat
multimatch goal with
| H : ?x == ?y |- _ => rewrite <- ?H in *
| H : ?x == ?x |- _ => clear H
end.

Ltac reflect_cmon' := cbn; intros; cmon_subst;
match goal with
| X : ComMon |- ?e1 == ?e2 => reify X; apply simplify_correct; cbn; rewrite ?neutr_l, ?neutr_r
end.

Ltac reflect_cmon := reflect_cmon'; try reflexivity.

Ltac reflect_goal := cbn; intros;
match goal with
| X : ComMon |- ?e1 == ?e2 => reify X; apply flat_reflect_goal
end.

(* Lemma cons_nil_all :
  forall (A : Type) (h h' : A),
    [h] = [h'] -> forall l : list A, cons h l = cons h' l.
Proof.
  now inversion 1.
Qed. *)

Goal forall (X : ComMon) (a b c : X),
  op a (op b c) == op (op a b) c.
Proof.
  reflect_cmon.
Qed.

Goal forall (X : ComMon) (a b : X),
  op a b == op b a.
Proof.
  reflect_cmon.
Qed.

Goal forall (X : ComMon) (a b b' c : X),
  b == b' -> op a (op b c) == op (op a b') c.
Proof.
  now reflect_cmon'.
Qed.

Goal forall (X : ComMon) (a a' b b' c c' : X),
  op a b == op a b' -> op (op a b) c == op b' (op a c).
Proof.
  reflect_cmon'. rewrite ?assoc. rewrite (com b').
  rewrite !H. now reflect_cmon'.
Qed.

Goal forall (X : ComMon) (a a' b b' c c' : X),
  a == b -> b == c -> c == a -> op b (op a c) == op a (op neutr (op b c)).
Proof.
  now reflect_cmon'.
Qed.

Inductive formula (X : ComMon) : Type :=
| fVar   : Prop -> formula X
| fEquiv : exp X -> exp X -> formula X
| fNot   : formula X -> formula X
| fAnd   : formula X -> formula X -> formula X
| fOr    : formula X -> formula X -> formula X
| fImpl  : formula X -> formula X -> formula X.

Arguments fVar {X} _.

Fixpoint formulaDenote {X : ComMon} (env : nat -> X) (p : formula X)
  : Prop :=
match p with
| fVar P       => P
| fEquiv e1 e2 => expDenote env e1 == expDenote env e2
| fNot p'      => ~ formulaDenote env p'
| fAnd p1 p2   => formulaDenote env p1 /\ formulaDenote env p2
| fOr p1 p2    => formulaDenote env p1 \/ formulaDenote env p2
| fImpl p1 p2  => formulaDenote env p1 -> formulaDenote env p2
end.

Ltac allVarsFormula xs P :=
match P with
| ?a == ?b => allVars xs P
| ~ ?P' => allVarsFormula xs P'
| ?P1 /\ ?P2 => let xs' := allVarsFormula xs P1 in allVarsFormula xs' P2
| ?P1 \/ ?P2 => let xs' := allVarsFormula xs P1 in allVarsFormula xs' P2
| ?P1 -> ?P2 => let xs' := allVarsFormula xs P1 in allVarsFormula xs' P2
| _ => xs
end.

Ltac reifyFormula X xs P :=
match P with
| ~ ?P' => let e := reifyFormula X xs P' in constr:(fNot e)
| ?a == ?b =>
  let e1 := reifyTerm xs a in
  let e2 := reifyTerm xs b in constr:(fEquiv e1 e2)
| ?P1 /\ ?P2 =>
  let e1 := reifyFormula X xs P1 in
  let e2 := reifyFormula X xs P2 in constr:(fAnd e1 e2)
| ?P1 \/ ?P2 =>
  let e1 := reifyFormula X xs P1 in
  let e2 := reifyFormula X xs P2 in constr:(fOr e1 e2)
| ?P1 -> ?P2 =>
  let e1 := reifyFormula X xs P1 in
  let e2 := reifyFormula X xs P2 in constr:(fImpl e1 e2)
| _ => constr:(fVar X P)
end.

Ltac reifyGoal :=
match goal with
| X : ComMon |- ?P =>
  let xs := allVarsFormula constr:(@nil X) P in
  let env := functionalize xs X in
  let e := reifyFormula X xs P in change (formulaDenote env e)
end.

Definition list_eq :
  forall (l1 l2 : list nat), {l1 = l2} + {l1 <> l2}.
Proof.
  do 2 decide equality.
Defined.

Fixpoint solveFormula {X : ComMon} (env : nat -> X) (f : formula X)
  : option (formulaDenote env f).
Proof.
  destruct f; cbn.
    apply None.
    destruct (list_eq
              (insertionSort natle (flatten (simplifyExp e)))
              (insertionSort natle (flatten (simplifyExp e0)))).
      apply Some. now apply simplify_correct.
      apply None.
    apply None.
    destruct (solveFormula X env f1), (solveFormula X env f2).
      now apply Some.
      1-3: apply None.
    destruct (solveFormula X env f1).
      apply Some. now left.
      destruct (solveFormula X env f2).
        apply Some. now right.
        apply None.
    destruct (solveFormula X env f2).
      apply Some. now intro.
      apply None.
Defined.

Lemma solveFormula_spec :
  forall (X : ComMon) (env : nat -> X) (f : formula X),
    (exists p : formulaDenote env f, solveFormula env f = Some p) ->
      formulaDenote env f.
Proof.
  intros. now destruct H.
Qed.

Ltac solve_goal' :=
  cbn; intros; cmon_subst; reifyGoal;
  apply solveFormula_spec; cbn; eauto.

Ltac solve_goal :=
  try (solve_goal'; fail);
  fail "Cannot solve the goal".

Goal forall (X : ComMon) (a a' b b' c c' : X),
  a == b -> b == c -> c == a -> a == c /\ op c c == op b b.
Proof.
  solve_goal.
Qed.

Goal forall (X : ComMon) (a a' b b' c c' : X),
  a == b -> b' == c' -> 2 = 2 \/ op c c == op c (op a c').
Proof.
  intros X a _ b b' c c'.
  match goal with
  | X : ComMon |- ?P =>
    let xs := allVarsFormula constr:(@nil X) P in
    let env := functionalize xs X in
    let f := fresh "f" in
    let f' := constr:(@formulaDenote X env) in pose f' as f
  end; cbn in *.
Abort.
*)

(*
#[refine]
#[export]
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

Definition Mon_fpair (A B X : Mon) (f : MonHom X A) (g : MonHom X B)
    : MonHom X (Mon_prodOb A B).
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
  formulaer.
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
  formulaer. all: mon.
Defined.

Notation "'U'" := forgetful.

Definition free_monoid
  (X : Ob CoqSetoid) (M : Mon) (p : Hom X (fob U M)) : Prop :=
    forall (N : Mon) (q : SetoidHom X (fob U N)),
      exists!! h : MonHom M N, q == p .> fmap U h.

#[refine]
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
  cbn. exists (fun _ => 1). formulaer.
Defined.

Lemma free_monoid_MonListUnit :
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
    Proper_func := ltac: (formulaer; subst; easy)
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
    formulaer. now subst.
  Defined.
  Definition f2 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : SgrHom MonListUnit N.
    exists (f1 N q). induction x as [| x']. simpl.
      mon.
      simpl. intro. now rewrite <- assoc, -> IHx'.
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
        rewrite H'. rewrite -> pres_op in H'. rewrite <- H', IHn'. f_equiv; mon.
Defined.*)