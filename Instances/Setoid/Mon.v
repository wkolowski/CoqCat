From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Zero Product Coproduct.
From Cat Require Export Instances.Setoid.Sgr.

Set Implicit Arguments.

Class Mon : Type :=
{
  sgr :> Sgr;
  neutr : sgr;
  neutr_l : forall a : sgr, op neutr a == a;
  neutr_r : forall a : sgr, op a neutr == a
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
  induction e; cbn; [easy | easy | |].
  - now destruct (simplify e1), (simplify e2); cbn in *;
      rewrite <- ?IHe1, <- ?IHe2, ?neutr_l, ?neutr_r.
  - now destruct (simplify e); cbn in *; rewrite <- ?IHe, ?pres_neutr, ?pres_op.
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
  - now rewrite neutr_l.
  - now rewrite <- assoc, IHt1.
Qed.

Lemma expDenoteL_hom :
  forall (X Y : Mon) (f : MonHom X Y) (l : list X),
    expDenoteL (map f l) == f (expDenoteL l).
Proof.
  induction l as [| h t]; cbn.
  - now rewrite pres_neutr.
  - now rewrite pres_op, IHt.
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
  induction e; cbn; [easy | | |].
  - now rewrite neutr_r.
  - now rewrite expDenoteL_app, IHe1, IHe2.
  - now rewrite expDenoteL_hom, IHe.
Qed.

Lemma mon_reflect :
  forall (X : Mon) (e1 e2 : exp X),
    expDenoteL (flatten (simplify e1)) == expDenoteL (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  now intros; rewrite !flatten_correct, !simplify_correct in H.
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
Proof. easy. Defined.

#[refine]
#[export]
Instance ReifyOp (X : Mon) (a b : X) (Ra : Reify a) (Rb : Reify b) : Reify (@op X a b) | 0 :=
{
  reify := Op (reify a) (reify b)
}.
Proof.
  now cbn; rewrite !reify_spec.
Defined.

#[refine]
#[export]
Instance ReifyHom (X Y : Mon) (f : MonHom X Y) (x : X) (Rx : Reify x) : Reify (f x) | 0 :=
{
  reify := Mor f (reify x)
}.
Proof.
  now cbn; rewrite reify_spec.
Defined.

#[refine]
#[export]
Instance ReifyId (X : Mon) : Reify neutr | 0 :=
{
  reify := Id
}.
Proof.
  easy.
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
| MonHom _ _ => let a := fresh f "_pres_neutr" in destruct f as [f a]
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
| |- _ == _ => now reflect_mon
| |- Equivalence _ => solve_equiv
| |- Proper _ _ => proper
| |- (_, _) = (_, _) => f_equal
| _ => mon_simpl || monobs' || monhoms' || cat
end.

Goal
  forall (X : Mon) (a b c : X),
    op a (op b c) == op (op a b) c.
Proof.
  now reflect_mon.
Qed.

Goal
  forall (X : Mon) (f : MonHom X X) (a b : X),
    f (op a b) == op (f a) (f b).
Proof.
  now reflect_mon.
Qed.

Goal
  forall (X : Mon) (f : MonHom X X) (a b c : X),
    op (f (f neutr)) (op (f a) (f (op b c))) == op (f a) (op (f b) (f c)).
Proof.
  now reflect_mon.
Qed.

Goal
  forall (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z),
    g (f neutr) == neutr.
Proof.
  now reflect_mon.
Qed.

(* TODO : improve reflection *)
Lemma flat_reflect_goal :
  forall (X : Mon) (e1 e2 : exp X),
    flatten (simplify e1) = flatten (simplify e2) ->
      expDenote e1 == expDenote e2.
Proof.
  now intros; apply mon_reflect; rewrite H.
Qed.

Lemma flat_reflect_hyp :
  forall (X : Mon) (e1 e2 : exp X),
    expDenote e1 == expDenote e2 ->
      flatten (simplify e1) = flatten (simplify e2).
Proof.
Admitted.

Lemma flat_reflect_hyp' :
  forall (X : Mon) (e1 e2 : exp X),
    expDenote e1 == expDenote e2 ->
      expDenoteL (flatten (simplify e1)) == expDenoteL (flatten (simplify e2)).
Proof.
  now intros; rewrite !flatten_correct, !simplify_correct.
Qed.

Ltac reflect_goal := cbn; intros;
match goal with
| |- ?e1 == ?e2 =>
  change (expDenote (reify e1) == expDenote (reify e2));
    apply flat_reflect_goal
end.

Lemma cons_nil_all :
  forall (A : Type) (h h' : A),
    [h] = [h'] -> forall l : list A, cons h l = cons h' l.
Proof.
  now inversion 1.
Qed.

Goal
  forall (X : Mon) (a b b' c : X),
    b == b' -> op a (op b c) == op (op a b') c.
Proof.
  intros.
  reflect_goal; cbn.
  match goal with
  | H : ?x == ?y |- _ =>
    change (expDenote (reify x) == expDenote (reify y)) in H;
      apply flat_reflect_hyp in H; cbn in H
  end.
  now inversion H; subst.
Abort.

#[refine]
#[export]
Instance MonHomSetoid (X Y : Mon) : Setoid (MonHom X Y) :=
{
  equiv := fun f g : MonHom X Y =>
    @equiv _ (SgrHomSetoid X Y) f g
}.
Proof. now apply Setoid_kernel_equiv. Defined.

Definition MonComp (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z) : MonHom X Z.
Proof.
  exists (SgrComp f g); cbn.
  now rewrite !pres_neutr.
Defined.

Definition MonId (X : Mon) : MonHom X X.
Proof.
  now exists (SgrId X).
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
Proof. all: now mon. Defined.

#[refine]
#[export]
Instance Mon_init : Mon :=
{
  sgr := Sgr_term;
  neutr := tt
}.
Proof. all: now mon. Defined.

Definition Mon_Setoid_create (X : Mon) : SetoidHom Mon_init X.
Proof.
  now exists (fun _ => neutr); proper.
Defined.

Definition Mon_Sgr_create (X : Mon) : SgrHom Mon_init X.
Proof.
  exists (Mon_Setoid_create X); cbn.
  now intros; symmetry; apply neutr_l.
Defined.

Definition Mon_create (X : Mon) : Hom Mon_init X.
Proof.
  now exists (Mon_Sgr_create X).
Defined.

#[refine]
#[export]
Instance HasInit_Mon : HasInit MonCat :=
{
  init := Mon_init;
  create := Mon_create
}.
Proof. now mon. Defined.

#[refine]
#[export]
Instance Mon_term : Mon :=
{
  sgr := Sgr_term;
  neutr := tt
}.
Proof. all: now mon. Defined.

Definition Mon_Setoid_delete (X : Mon) : SetoidHom X Mon_term.
Proof.
  now exists (fun _ => tt); proper.
Defined.

Definition Mon_Sgr_delete (X : Mon) : SgrHom X Mon_term.
Proof.
  now exists (Mon_Setoid_delete X).
Defined.

Definition Mon_delete (X : Mon) : Hom X Mon_term.
Proof.
  now exists (Mon_Sgr_delete X).
Defined.

#[refine]
#[export]
Instance HasTerm_Mon : HasTerm MonCat :=
{
  term := Mon_term;
  delete := Mon_delete
}.
Proof. now mon. Defined.

#[refine]
#[export]
Instance HasZero_Mon : HasZero MonCat :=
{
  HasInit_HasZero := HasInit_Mon;
  HasTerm_HasZero := HasTerm_Mon
}.
Proof. now mon. Defined.

#[refine]
#[export]
Instance Mon_product (X Y : Mon) : Mon :=
{
  sgr := Sgr_product X Y;
  neutr := (neutr, neutr);
}.
Proof. all: now destruct a; mon. Defined.

Definition Mon_outl (X Y : Mon) : Hom (Mon_product X Y) X.
Proof.
  now exists (Sgr_outl X Y).
Defined.

Definition Mon_outr (X Y : Mon) : Hom (Mon_product X Y) Y.
Proof.
  now exists (Sgr_outr X Y).
Defined.

Definition Mon_fpair
  (A B X : Mon) (f : MonHom X A) (g : MonHom X B) : MonHom X (Mon_product A B).
Proof.
  exists (Sgr_fpair f g); cbn.
  now rewrite !pres_neutr.
Defined.

#[refine]
#[export]
Instance HasProducts_Mon : HasProducts MonCat :=
{
  product := Mon_product;
  outl := Mon_outl;
  outr := Mon_outr;
  fpair := Mon_fpair
}.
Proof.
  now repeat split; cbn in *; intros.
Defined.

#[refine]
#[export]
Instance forgetful : Functor MonCat CoqSetoid :=
{
  fob := fun X : Mon => @setoid (sgr X);
  fmap := fun (A B : Mon) (f : Hom A B) => f;
}.
Proof.
  - now proper.
  - now cbn.
  - now cbn.
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
  all: now cbn; intros; lia.
Defined.

Definition MonListUnit_p : SetoidHom CoqSetoid_term MonListUnit.
Proof.
  exists (fun _ => 1).
  now proper.
Defined.

Set Nested Proofs Allowed.

Lemma free_monoid_MonListUnit :
  @free_monoid CoqSetoid_term MonListUnit MonListUnit_p.
Proof.
  unfold free_monoid. intros.
  Definition f1 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : SetoidHom MonListUnit N.
  Proof.
    exists (fix f (n : nat) : N :=
      match n with
      | 0 => @neutr N
      | S n' => op (q tt) (f n')
      end).
    now proper; subst.
  Defined.
  Definition f2 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : SgrHom MonListUnit N.
  Proof.
    exists (f1 N q).
    induction x as [| x']; intros.
    - now cbn; rewrite neutr_l.
    - now cbn; rewrite <- assoc, -> IHx'.
  Defined.
  Definition f3 (N : Mon) (q : SetoidHom CoqSetoid_term (fob U N))
    : MonHom MonListUnit N.
  Proof.
    now exists (f2 N q).
  Defined.
  exists (f3 N q).
  repeat split.
  - now cbn; intros []; rewrite neutr_r.
  - intros [[y H1] H2] Heq n; cbn in *.
    induction n as [| n'].
    + now rewrite H2.
    + change (S n') with (1 + n')%nat.
      now rewrite H1, Heq, IHn'.
Defined.

Inductive MCE {A B : Mon} : list (A + B) -> list (A + B) -> Prop :=
| MCE_nil : MCE [] []
| MCE_inl :
  forall (a1 a2 : A) (t1 t2 : list (A + B)),
    a1 == a2 -> MCE t1 t2 -> MCE (inl a1 :: t1) (inl a2 :: t2)
| MCE_inr :
  forall (b1 b2 : B) (t1 t2 : list (A + B)),
    b1 == b2 -> MCE t1 t2 -> MCE (inr b1 :: t1) (inr b2 :: t2)
| MCE_refl :
  forall l : list (A + B), MCE l l
| MCE_sym :
  forall l1 l2 : list (A + B),
    MCE l1 l2 -> MCE l2 l1
| MCE_trans :
  forall l1 l2 l3 : list (A + B),
    MCE l1 l2 -> MCE l2 l3 -> MCE l1 l3
| MCE_nil_neutr_l : forall t : list (A + B), MCE (inl neutr :: t) t
| MCE_nil_neutr_r : forall t : list (A + B), MCE (inr neutr :: t) t
| MCE_cons_op_l :
  forall (a1 a2 : A) (t : list (A + B)),
    MCE (inl a1 :: inl a2 :: t) (inl (op a1 a2) :: t)
| MCE_cons_op_r :
  forall (b1 b2 : B) (t : list (A + B)),
    MCE (inr b1 :: inr b2 :: t) (inr (op b1 b2) :: t).

#[export] Hint Constructors MCE : core.

#[export]
Instance Equivalence_MCE :
  forall A B : Mon,
    Equivalence (@MCE A B).
Proof.
  split; red.
  - now apply MCE_refl.
  - now apply MCE_sym.
  - now apply MCE_trans.
Defined.

Lemma MCE_app_l :
  forall (A B : Mon) (l l1 l2 : list (A + B)),
    MCE l1 l2 -> MCE (l ++ l1) (l ++ l2).
Proof.
  induction l as [| [a | b] t]; cbn; intros; [easy | |].
  - now constructor; [| apply IHt].
  - now constructor; [| apply IHt].
Qed.

Lemma MCE_app :
  forall {A B : Mon} (l11 l12 l21 l22 : list (A + B)),
    MCE l11 l12 -> MCE l21 l22 -> MCE (l11 ++ l21) (l12 ++ l22).
Proof.
  intros * H1 H2; revert l21 l22 H2.
  induction H1; cbn; intros.
  - easy.
  - now eauto.
  - now eauto.
  - now apply MCE_app_l.
  - now eauto.
  - now transitivity (l2 ++ l22); eauto.
  - rewrite MCE_nil_neutr_l.
    now apply MCE_app_l.
  - rewrite MCE_nil_neutr_r.
    now apply MCE_app_l.
  - rewrite MCE_cons_op_l.
    constructor; [easy |].
    now apply MCE_app_l.
  - rewrite MCE_cons_op_r.
    constructor; [easy |].
    now apply MCE_app_l.
Defined.

#[export]
Instance Mon_coproduct_Setoid' (A B : Mon) : Setoid' :=
{
  carrier := list (A + B);
  setoid :=
  {|
    equiv := MCE;
    setoid_equiv := Equivalence_MCE A B;
  |};
}.

#[refine]
#[export]
Instance Mon_coproduct_Sgr (A B : Mon) : Sgr :=
{
  setoid := Mon_coproduct_Setoid' A B;
  op := fun l1 l2 => l1 ++ l2;
}.
Proof.
  - intros l1 l1' H1 l2 l2' H2; cbn in *.
    now apply MCE_app.
  - now cbn; intros; rewrite app_assoc.
Defined.

#[refine]
#[export]
Instance Mon_coproduct (A B : Mon) : Mon :=
{
  sgr := Mon_coproduct_Sgr A B;
  neutr := [];
}.
Proof.
  - easy.
  - now cbn; intros; rewrite app_nil_r.
Defined.

#[export]
Instance Mon_finl_Setoid' (A B : Mon) : SetoidHom A (Mon_coproduct A B).
Proof.
  split with (fun a => [inl a]).
  now constructor.
Defined.

#[export]
Instance Mon_finl_Sgr (A B : Mon) : SgrHom A (Mon_coproduct A B).
Proof.
  split with (Mon_finl_Setoid' A B); cbn.
  now intros; rewrite MCE_cons_op_l.
Defined.

#[export]
Instance Mon_finl {A B : Mon} : MonHom A (Mon_coproduct A B).
Proof.
  split with (Mon_finl_Sgr A B); cbn.
  now rewrite MCE_nil_neutr_l.
Defined.

#[export]
Instance Mon_finr_Setoid' (A B : Mon) : SetoidHom B (Mon_coproduct A B).
Proof.
  split with (fun b => [inr b]).
  now constructor.
Defined.

#[export]
Instance Mon_finr_Sgr (A B : Mon) : SgrHom B (Mon_coproduct A B).
Proof.
  esplit with (Mon_finr_Setoid' A B); cbn.
  now intros; rewrite MCE_cons_op_r.
Defined.

#[export]
Instance Mon_finr {A B : Mon} : MonHom B (Mon_coproduct A B).
Proof.
  esplit with (Mon_finr_Sgr A B); cbn.
  now rewrite MCE_nil_neutr_r.
Defined.

Fixpoint Mon_copair'
  {A B X : Mon} (f : MonHom A X) (g : MonHom B X) (l : list (A + B)) : X :=
match l with
| [] => neutr
| inl a :: t => op (f a) (Mon_copair' f g t)
| inr b :: t => op (g b) (Mon_copair' f g t)
end.

Lemma Mon_copair'_app :
  forall {A B X : Mon} (f : MonHom A X) (g : MonHom B X) (l1 l2 : list (A + B)),
    Mon_copair' f g (l1 ++ l2) == op (Mon_copair' f g l1) (Mon_copair' f g l2).
Proof.
  induction l1 as [| h1 t1]; cbn; intros l2.
  - now rewrite neutr_l.
  - now destruct h1 as [a | b]; cbn; rewrite IHt1, <- assoc.
Qed.

#[export]
Instance Mon_copair_Setoid'
  {A B X : Mon} (f : MonHom A X) (g : MonHom B X) : SetoidHom (Mon_coproduct A B) X.
Proof.
  esplit with (Mon_copair' f g).
  intros l1 l2 Heq; cbn in *.
  induction Heq; cbn.
  - easy.
  - now rewrite IHHeq, H.
  - now rewrite IHHeq, H.
  - easy.
  - easy.
  - now rewrite IHHeq1, IHHeq2.
  - now rewrite pres_neutr, neutr_l.
  - now rewrite pres_neutr, neutr_l.
  - now rewrite pres_op, <- assoc.
  - now rewrite pres_op, <- assoc.
Defined.

#[export]
Instance Mon_copair_Sgr
  {A B X : Mon} (f : MonHom A X) (g : MonHom B X) : SgrHom (Mon_coproduct A B) X.
Proof.
  esplit with (Mon_copair_Setoid' f g); cbn.
  now intros; rewrite Mon_copair'_app.
Defined.

#[export]
Instance Mon_copair
  {A B X : Mon} (f : MonHom A X) (g : MonHom B X) : MonHom (Mon_coproduct A B) X.
Proof.
  now esplit with (Mon_copair_Sgr f g).
Defined.

#[refine]
#[export]
Instance HasCoproducts_Mon : HasCoproducts MonCat :=
{
  coproduct := @Mon_coproduct;
  finl := @Mon_finl;
  finr := @Mon_finr;
  copair := @Mon_copair;
}.
Proof.
  split; cbn.
  - now intros; rewrite neutr_r.
  - now intros; rewrite neutr_r.
  - intros P' h1 h2 HA HB l.
    induction l as [| h t]; cbn.
    + now rewrite <- MCE_nil_neutr_l, HA.
    + change (h :: t) with (@op (Mon_coproduct A B) [h] t).
      now rewrite (@pres_op _ _ h1), (@pres_op _ _ h2), IHt; destruct h; rewrite ?HA, ?HB.
Defined.

#[refine]
#[export]
Instance Mon_equalizer {A B : Mon} (f g : MonHom A B) : Mon :=
{
  sgr := Sgr_equalizer f g;
}.
Proof.
  - exists neutr.
    now rewrite !pres_neutr.
  - intros [a H]; cbn.
    now rewrite neutr_l.
  - intros [a H]; cbn.
    now rewrite neutr_r.
Defined.

#[refine]
#[export]
Instance Mon_equalize {A B : Mon} (f g : MonHom A B) : MonHom (Mon_equalizer f g) A :=
{
  sgrHom := Sgr_equalize f g;
}.
Proof.
  now cbn.
Defined.

#[refine]
#[export]
Instance Mon_factorize
  {A B : Mon} {f g : MonHom A B}
  {E' : Mon} (e' : Hom E' A) (Heq : (e' .> f) == (e' .> g))
  : MonHom E' (Mon_equalizer f g) :=
{
  sgrHom := Sgr_factorize Heq;
}.
Proof.
  now cbn; rewrite pres_neutr.
Defined.

#[refine]
#[export]
Instance HasEqualizers_Mon : HasEqualizers MonCat :=
{
  equalizer := @Mon_equalizer;
  equalize  := @Mon_equalize;
  factorize := @Mon_factorize;
}.
Proof.
  split; cbn.
  - now intros [x H]; cbn.
  - easy.
  - easy.
Defined.

#[refine]
#[export]
Instance Mon_coequalizer {A B : Mon} (f g : MonHom A B) : Mon :=
{
  sgr := Sgr_coequalizer f g;
  neutr := neutr;
}.
Proof.
  - now constructor; cbn; rewrite neutr_l.
  - now constructor; cbn; rewrite neutr_r.
Defined.

#[refine]
#[export]
Instance Mon_coequalize {A B : Mon} {f g : MonHom A B} : MonHom B (Mon_coequalizer f g) :=
{
  sgrHom := @Sgr_coequalize A B f g;
}.
Proof.
  now cbn.
Defined.

#[export]
#[refine]
Instance Mon_cofactorize
  {A B : Mon} {f g : Hom A B}
  {Q : Mon} (q : Hom B Q) (Heq : f .> q == g .> q)
  : MonHom (Mon_coequalizer f g) Q :=
{
  sgrHom := Sgr_cofactorize Heq;
}.
Proof.
  now cbn; rewrite pres_neutr.
Defined.

#[refine]
#[export]
Instance HasCoequalizers_Mon : HasCoequalizers MonCat :=
{
  coequalizer := @Mon_coequalizer;
  coequalize  := @Mon_coequalize;
  cofactorize := @Mon_cofactorize;
}.
Proof.
  split; cbn.
  - now constructor.
  - easy.
  - easy.
Defined.

#[refine]
#[export]
Instance Mon_pullback
  {A B X : Mon} (f : MonHom A X) (g : MonHom B X) : Mon :=
{
  sgr := Sgr_pullback f g;
}.
Proof.
  - refine {| pullL := neutr; pullR := neutr; |}.
    now rewrite !pres_neutr.
  - intros [a b H]; cbn.
    now rewrite !neutr_l.
  - intros [a b H]; cbn.
    now rewrite !neutr_r.
Defined.

#[refine]
#[export]
Instance Mon_pullL
  {A B X : Mon} (f : MonHom A X) (g : MonHom B X) : MonHom (Mon_pullback f g) A :=
{
  sgrHom := Sgr_pullL f g;
}.
Proof.
  now cbn.
Defined.

#[refine]
#[export]
Instance Mon_pullR
  {A B X : Mon} (f : MonHom A X) (g : MonHom B X) : MonHom (Mon_pullback f g) B :=
{
  sgrHom := Sgr_pullR f g;
}.
Proof.
  now cbn.
Defined.

#[refine]
#[export]
Instance Mon_triple
  {A B X : Mon} (f : Hom A X) (g : Hom B X)
  {Γ : Mon} (a : Hom Γ A) (b : Hom Γ B) (Heq : a .> f == b .> g)
  : MonHom Γ (Mon_pullback f g) :=
{
  sgrHom := Sgr_triple Heq;
}.
Proof.
  now cbn; rewrite !pres_neutr.
Defined.

#[refine]
#[export]
Instance HasPullbacks_Mon : HasPullbacks MonCat :=
{
  pullback := @Mon_pullback;
  pullL    := @Mon_pullL;
  pullR    := @Mon_pullR;
  triple   := @Mon_triple;
}.
Proof.
  split; cbn.
  - now apply ok.
  - easy.
  - easy.
  - now split.
Defined.

(* We construct pushouts from coproducts and coequalizers. *)
#[export] Instance HasPushouts_Mon : HasPushouts MonCat :=
  HasPushouts_HasCoproducts_HasCoequalizers HasCoproducts_Mon HasCoequalizers_Mon.