From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct.
From Cat Require Export Instances.Setoids.

Set Implicit Arguments.

Class Sgr : Type :=
{
  setoid :> Setoid';
  op : carrier -> carrier -> carrier;
  Proper_op :> Proper (equiv ==> equiv ==> equiv) op;
  assoc : forall x y z : carrier, op x (op y z) == op (op x y) z
}.

Coercion setoid : Sgr >-> Setoid'.

Class SgrHom (A B : Sgr) : Type :=
{
  setoidHom :> SetoidHom A B;
  pres_op : forall x y : A, setoidHom (op x y) == op (setoidHom x) (setoidHom y)
}.

Coercion setoidHom : SgrHom >-> SetoidHom.

Inductive exp (X : Sgr) : Type :=
| Var : X -> exp X
| Op : exp X -> exp X -> exp X
| Mor : forall A : Sgr, SgrHom A X -> exp A -> exp X.

Arguments Var [X] _.
Arguments Op [X] _ _.
Arguments Mor [X A] _ _ .

Fixpoint expDenote {X : Sgr} (e : exp X) : X :=
match e with
| Var v => v
| Op e1 e2 => op (expDenote e1) (expDenote e2)
| Mor f e' => f (expDenote e')
end.

Fixpoint simplify {X : Sgr} (e : exp X) : exp X :=
match e with
| Var v => Var v
| Op e1 e2 => Op (simplify e1) (simplify e2)
| Mor f e' =>
  match simplify e' with
  | Op e1' e2' => Op (Mor f e1') (Mor f e2')
  | e'' => Mor f e''
  end
end.

Lemma simplify_correct :
  forall (X : Sgr) (e : exp X),
    expDenote (simplify e) == expDenote e.
Proof.
  induction e; cbn; [easy | |].
  - now rewrite IHe1, IHe2.
  - now destruct (simplify e); cbn in *; rewrite <- IHe, ?pres_op.
Qed.

Fixpoint expDenoteNel {X : Sgr} (l : nel X) : X :=
match l with
| singl x => x
| h ::: t => op h (expDenoteNel t)
end.

Lemma expDenoteNel_nel_app :
  forall (X : Sgr) (l1 l2 : nel X),
    expDenoteNel (nel_app l1 l2) == op (expDenoteNel l1) (expDenoteNel l2).
Proof.
  induction l1 as [| h1 t1]; cbn; intros; [easy |].
  now rewrite IHt1, assoc.
Qed.

Lemma expDenoteNel_hom :
  forall (X Y : Sgr) (f : SgrHom X Y) (l : nel X),
    expDenoteNel (nel_map f l) == f (expDenoteNel l).
Proof.
  induction l as [| h t]; cbn; [easy |].
  now rewrite pres_op, IHt.
Qed.

Fixpoint flatten {X : Sgr} (e : exp X) : nel X :=
match e with
| Var v => singl v
| Op e1 e2 => nel_app (flatten e1) (flatten e2)
| Mor f e' => nel_map f (flatten e')
end.

Lemma flatten_correct :
  forall (X : Sgr) (e : exp X),
    expDenoteNel (flatten e) == expDenote e.
Proof.
  induction e; cbn; [easy | |].
  - now rewrite expDenoteNel_nel_app, IHe1, IHe2.
  - now rewrite expDenoteNel_hom, IHe.
Qed.

Lemma sgr_reflect :
  forall (X : Sgr) (e1 e2 : exp X),
    expDenoteNel (flatten (simplify e1)) ==
    expDenoteNel (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  now intros; rewrite !flatten_correct, !simplify_correct in H.
Qed.

Class Reify (X : Sgr) (x : X) : Type :=
{
  reify : exp X;
  reify_spec : expDenote reify == x
}.

Arguments Reify {X} _.
Arguments reify {X} _ {Reify}.

#[refine]
#[export]
Instance ReifyVar (X : Sgr) (x : X) : Reify x | 1 :=
{
  reify := Var x
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance ReifyOp (X : Sgr) (a b : X) (Ra : Reify a) (Rb : Reify b) : Reify (@op X a b) | 0 :=
{
  reify := Op (reify a) (reify b)
}.
Proof.
  now cbn; rewrite !reify_spec.
Defined.

#[refine]
#[export]
Instance ReifyMor (X Y : Sgr) (f : SgrHom X Y) (x : X) (Rx : Reify x) : Reify (f x) | 0 :=
{
  reify := Mor f (reify x)
}.
Proof.
  now cbn; rewrite !reify_spec.
Defined.

Ltac reflect_sgr := cbn; intros;
match goal with
| |- ?e1 == ?e2 =>
  change (expDenote (reify e1) == expDenote (reify e2));
  apply sgr_reflect; cbn
end.

Ltac reflect_sgr' :=
  intros;
  do 2 (rewrite <- reify_spec; symmetry);
  apply sgr_reflect; cbn.

Ltac sgr_simpl := repeat red; cbn in *; intros.

Ltac sgrob S := try intros until S;
match type of S with
| Sgr =>
  let a := fresh S "_op" in
  let a' := fresh S "_Proper_op" in 
  let b := fresh S "_assoc" in destruct S as [S a a' b]; setoidob S
| Ob _ => progress cbn in S; sgrob S
end; sgr_simpl.

Ltac sgrobs := repeat
match goal with
| S : Sgr |- _ => sgrob S
| S : Ob _ |- _ => sgrob S
end; sgr_simpl.

Ltac sgrhom f := try intros until f;
match type of f with
| SgrHom _ _ =>
    let a := fresh f "_pres_op" in destruct f as [f a];
    cbn in *; setoidhom f
| Hom _ _ => progress cbn in f; sgrhom f
end; sgr_simpl.

Ltac sgrhoms := intros; repeat
match goal with
| f : SgrHom _ _ |- _ => sgrhom f
| f : Hom _ _ |- _ => sgrhom f
| _ => idtac
end; sgr_simpl.

Ltac sgr := intros; try (reflect_sgr; try reflexivity; fail); repeat
match goal with
| |- _ == _ => now reflect_sgr
| |- Equivalence _ => solve_equiv
| |- Proper _ _ => proper
| _ => sgr_simpl || sgrobs || sgrhoms || cat
end.

Goal
  forall (X : Sgr) (a b c : X),
    op a (op b c) == op (op a b) c.
Proof.
  now reflect_sgr.
Qed.

Goal
  forall (X : Sgr) (f : SgrHom X X) (a b : X),
    f (op a b) == op (f a) (f b).
Proof.
  now reflect_sgr.
Qed.

#[refine]
#[export]
Instance SgrHomSetoid (X Y : Sgr) : Setoid (SgrHom X Y) :=
{
  equiv := fun f g : SgrHom X Y => forall x : X, f x == g x
}.
Proof. now sgr. Defined.

Definition SgrComp (A B C : Sgr) (f : SgrHom A B) (g : SgrHom B C) : SgrHom A C.
Proof.
  exists (SetoidComp f g); cbn.
  now intros; rewrite !pres_op.
Defined.

Definition SgrId (A : Sgr) : SgrHom A A.
Proof.
  now exists (SetoidId A).
Defined.

#[refine]
#[export]
Instance SgrCat : Cat :=
{
  Ob := Sgr;
  Hom := SgrHom;
  HomSetoid := SgrHomSetoid;
  comp := SgrComp;
  id := SgrId
}.
Proof. all: now sgr. Defined.

#[refine]
#[export]
Instance Sgr_init : Sgr :=
{
  setoid := CoqSetoid_init;
  op := fun (e : Empty_set) _ => match e with end
}.
Proof. all: easy. Defined.

Definition Sgr_create (X : Sgr) : Hom Sgr_init X.
Proof.
  now exists (CoqSetoid_create X).
Defined.

#[refine]
#[export]
Instance HasInit_Sgr : HasInit SgrCat :=
{
  init := Sgr_init;
  create := Sgr_create
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance Sgr_term : Sgr :=
{
  setoid := CoqSetoid_term;
  op := fun _ _ => tt
}.
Proof. all: easy. Defined.

Definition Sgr_delete (X : Sgr) : Hom X Sgr_term.
Proof.
  now exists (CoqSetoid_delete X).
Defined.

#[refine]
#[export]
Instance HasTerm_Sgr : HasTerm SgrCat :=
{
  term := Sgr_term;
  delete := Sgr_delete
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance Sgr_product (X Y : Sgr) : Sgr :=
{
  setoid := CoqSetoid_product X Y;
  op := fun x y => (op (fst x) (fst y), op (snd x) (snd y))
}.
Proof.
  - intros [f1 Hf1] [f2 Hf2] [Hf1' Hf2'] [g1 Hg1] [g2 Hg2] [Hg1' Hg2']; cbn in *.
    now rewrite Hf1', Hf2', Hg1', Hg2'.
  - intros [x1 y1] [x2 y2] [x3 y3]; cbn.
    now rewrite !assoc.
Defined.

Definition Sgr_outl (X Y : Sgr) : SgrHom (Sgr_product X Y) X.
Proof.
  now exists (CoqSetoid_outl X Y).
Defined.

Definition Sgr_outr (X Y : Sgr) : SgrHom (Sgr_product X Y) Y.
Proof.
  now exists (CoqSetoid_outr X Y).
Defined.

Definition Sgr_fpair (A B X : Sgr) (f : SgrHom X A) (g : SgrHom X B)
    : SgrHom X (Sgr_product A B).
Proof.
  exists (CoqSetoid_fpair f g); cbn.
  now intros; rewrite !pres_op.
Defined.

#[refine]
#[export]
Instance HasProducts_Sgr : HasProducts SgrCat :=
{
  product := Sgr_product;
  outl := Sgr_outl;
  outr := Sgr_outr;
  fpair := Sgr_fpair
}.
Proof.
  now repeat split; cbn in *.
Defined.

Module wut.

Inductive SCE {A B : Sgr} : nel (A + B) -> nel (A + B) -> Prop :=
| SCE_singl_l :
  forall a1 a2 : A, a1 == a2 -> SCE (singl (inl a1)) (singl (inl a2))
| SCE_singl_r :
  forall b1 b2 : B, b1 == b2 -> SCE (singl (inr b1)) (singl (inr b2))
| SCE_cons_l :
  forall (a1 a2 : A) (t1 t2 : nel (A + B)),
    a1 == a2 -> SCE t1 t2 -> SCE (inl a1 ::: t1) (inl a2 ::: t2)
| SCE_cons_r :
  forall (b1 b2 : B) (t1 t2 : nel (A + B)),
    b1 == b2 -> SCE t1 t2 -> SCE (inr b1 ::: t1) (inr b2 ::: t2)
| SCE_refl :
  forall l : nel (A + B), SCE l l
| SCE_sym :
  forall l1 l2 : nel (A + B),
    SCE l1 l2 -> SCE l2 l1
| SCE_trans :
  forall l1 l2 l3 : nel (A + B),
    SCE l1 l2 -> SCE l2 l3 -> SCE l1 l3
| SCE_cons_op_l :
  forall (a1 a2 : A) (t : nel (A + B)),
    SCE (inl a1 ::: inl a2 ::: t) (inl (op a1 a2) ::: t)
| SCE_cons_op_r :
  forall (b1 b2 : B) (t : nel (A + B)),
    SCE (inr b1 ::: inr b2 ::: t) (inr (op b1 b2) ::: t).

#[export] Hint Constructors SCE : core.

#[export]
Instance Equivalence_SCE :
  forall A B : Sgr,
    Equivalence (@SCE A B).
Proof.
  split; red.
  - now apply SCE_refl.
  - now apply SCE_sym.
  - now apply SCE_trans.
Defined.

Lemma SCE_app_l :
  forall (A B : Sgr) (l l1 l2 : nel (A + B)),
    SCE l1 l2 -> SCE (nel_app l l1) (nel_app l l2).
Proof.
  induction l as [[a | b] | [a | b] t]; cbn; intros.
  - now constructor.
  - now constructor.
  - now constructor; [| apply IHt].
  - now constructor; [| apply IHt].
Qed.

Lemma SCE_app :
  forall {A B : Sgr} (l11 l12 l21 l22 : nel (A + B)),
    SCE l11 l12 -> SCE l21 l22 -> SCE (nel_app l11 l21) (nel_app l12 l22).
Proof.
  intros * H1 H2; revert l21 l22 H2.
  induction H1; cbn; intros.
  - now eauto.
  - now eauto.
  - now eauto.
  - now eauto.
  - now apply SCE_app_l.
  - now eauto.
  - now eauto.
  - rewrite SCE_cons_op_l.
    constructor; [easy |].
    now apply SCE_app_l.
  - rewrite SCE_cons_op_r.
    constructor; [easy |].
    now apply SCE_app_l.
Defined.

#[export]
Instance Sgr_coproduct_Setoid' (A B : Sgr) : Setoid' :=
{
  carrier := nel (A + B);
  setoid :=
  {|
    equiv := SCE;
    setoid_equiv := Equivalence_SCE A B;
  |};
}.

#[refine]
#[export]
Instance Sgr_coproduct (A B : Sgr) : Sgr :=
{
  setoid := Sgr_coproduct_Setoid' A B;
  op := fun l1 l2 => nel_app l1 l2;
}.
Proof.
  - intros l1 l1' H1 l2 l2' H2; cbn in *.
    now apply SCE_app.
  - now cbn; intros; rewrite nel_app_assoc.
Defined.

#[export]
Instance Sgr_finl' (A B : Sgr) : SetoidHom A (Sgr_coproduct A B).
Proof.
  esplit. Unshelve. all: cycle 1.
  - exact (fun a => singl (inl a)).
  - now constructor.
Defined.

#[export]
Instance Sgr_finl (A B : Sgr) : SgrHom A (Sgr_coproduct A B).
Proof.
  esplit with (Sgr_finl' A B); cbn.
  intros; rewrite SCE_cons_op_l.
Defined.

#[export]
Instance Sgr_finr' (A B : Sgr) : SetoidHom B (Sgr_coproduct A B).
Proof.
  esplit. Unshelve. all: cycle 1.
  - exact (fun b => singl (inr b)).
  - now constructor.
Defined.

#[export]
Instance Sgr_finr (A B : Sgr) : SgrHom B (Sgr_coproduct A B).
Proof.
  esplit with (Sgr_finr' A B); cbn.
  now intros; rewrite SCE_cons_op_r.
Defined.

Fixpoint Sgr_copair'
  {A B X : Sgr} (f : SgrHom A X) (g : SgrHom B X) (l : nel (A + B)) : X :=
match l with
| singl (inl a) => f a
| singl (inr b) => g b
| inl a ::: t => op (f a) (Sgr_copair' f g t)
| inr b ::: t => op (g b) (Sgr_copair' f g t)
end.

Lemma Sgr_copair'_app :
  forall {A B X : Sgr} (f : SgrHom A X) (g : SgrHom B X) (l1 l2 : nel (A + B)),
    Sgr_copair' f g (nel_app l1 l2) == op (Sgr_copair' f g l1) (Sgr_copair' f g l2).
Proof.
  now induction l1 as [[a | b] | [a | b] t1]; cbn; intros l2; rewrite ?IHt1, ?assoc.
Qed.

Axiom cheat : False.

Fixpoint list2nel {A : Type} (x : A) (l : list A) : nel A :=
match l with
| [] => singl x
| [h] => singl h
| h :: t => h ::: list2nel x t
end.

(* Lemma nel2list2nel :
  forall {A : Type} (x : A) (l : nel A),
    list2nel x (nel2list l) = x ::: l.
Proof.
  intros A x l; revert x.
  now induction l as [h | h t]; cbn; intros; rewrite ?IHt.
Qed.
 *)

Definition hd {A : Type} (l : nel A) : A :=
match l with
| singl h => h
| h ::: _ => h
end.

Lemma nel2list2nel :
  forall {A : Type} (x : A) (l : nel A),
    list2nel x (nel2list l) = l.
Proof.
  intros A x l; revert x.
  induction l as [h | h t]; cbn; intros.
  - easy.
  - destruct (nel2list t) eqn: Heq.
    + now destruct t; inversion Heq.
    + now rewrite IHt.
Qed.

Lemma SCE_list2nel :
  forall {A B : Sgr} (x : A + B) (l1 l2 : list (A + B)),
    SCE l1 l2 -> SCE (nel2list (list2nel x l1)) (nel2list (list2nel x l2)).
Proof.
  intros A B x l1 l2 Heq; revert x.
  induction Heq; cbn; intros.
  - easy.
  - destruct t1, t2; cbn.
    + now constructor.
    + 
Abort.

#[export]
Instance Sgr_copair_Setoid'
  {A B X : Sgr} (f : SgrHom A X) (g : SgrHom B X) : SetoidHom (Sgr_coproduct A B) X.
Proof.
  esplit with (Sgr_copair' f g).
  intros l1 l2 Heq; cbn in *.
  rewrite <- (nel2list2nel (hd l1) l1),
          <- (nel2list2nel (hd l2) l2).
  generalize dependent (nel2list l1);
  generalize dependent (nel2list l2);
  generalize dependent (hd l1);
  generalize dependent (hd l2);
  clear l1 l2.
  intros z2 z1 l2 l1 Heq.
  induction Heq; cbn.
  - admit.
  - cbn in IHHeq.
Abort.

#[export]
Instance Sgr_copair
  {A B X : Sgr} (f : SgrHom A X) (g : SgrHom B X) : SgrHom (Sgr_coproduct A B) X.
Proof.
  esplit with (Sgr_copair_Setoid' f g); cbn.
  now intros; rewrite Sgr_copair'_app.
Defined.

#[refine]
#[export]
Instance HasCoproducts_Sgr : HasCoproducts SgrCat :=
{
  coproduct := @Sgr_coproduct;
  finl := @Sgr_finl;
  finr := @Sgr_finr;
  copair := @Sgr_copair;
}.
Proof.
  split; cbn.
  - easy.
  - easy.
  - intros P' h1 h2 HA HB l.
    induction l as [[a | b] | h t]; cbn.
    + now apply HA.
    + now apply HB.
    + change (h ::: t) with (@op (Sgr_coproduct A B) (singl h) t).
      now rewrite (@pres_op _ _ h1), (@pres_op _ _ h2), IHt; destruct h; rewrite ?HA, ?HB.
Defined.

Print Assumptions HasCoproducts_Sgr.

End wut.

Require Import Recdef.

Function normalize {X Y : Sgr} (l : nel (X + Y)) {struct l} : nel (X + Y) :=
match l with
| singl s => singl s
| inl x ::: singl (inl x') => singl (inl (op x x'))
| inr y ::: singl (inr y') => singl (inr (op y y'))
| inl _ ::: singl (inr _) => l
| inr _ ::: singl (inl _) => l
| inl x ::: t =>
  match normalize t with
  | singl (inl x') => singl (inl (op x x'))
  | inl x' ::: t' => inl (op x x') ::: t'
  | t' => inl x ::: t'
  end
| inr y ::: t =>
  match normalize t with
  | singl (inr y') => singl (inr (op y y'))
  | inr y' ::: t' => inr (op y y') ::: t'
  | t' => inr y ::: t'
  end
end.

Definition fpeq4 {X Y : Sgr} (l1 l2 : nel (X + Y)) : Prop :=
  fp_equiv (normalize l1) (normalize l2).

Ltac fpeq4 := unfold fpeq4; repeat
match goal with
| x : _ + _ |- _ => destruct x; cbn in *
| H : match normalize ?l with | _ => _ end |- _ => destruct (normalize l); cbn in *
| |- match normalize ?l with | _ => _ end => destruct (normalize l); cbn in *
| _ => solve_equiv
end.

Lemma fpeq4_refl :
  forall (X Y : Sgr) (l : nel (X + Y)),
    fpeq4 l l.
Proof.
  now induction l as [| h [| h' t]]; fpeq4.
Qed.

Lemma fpeq4_sym :
  forall (X Y : Sgr) (l1 l2 : nel (X + Y)),
    fpeq4 l1 l2 -> fpeq4 l2 l1.
Proof.
  now induction l1 as [| h [| h' t]]; fpeq4.
Qed.

Lemma fpeq4_trans :
  forall (X Y : Sgr) (l1 l2 l3 : nel (X + Y)),
    fpeq4 l1 l2 -> fpeq4 l2 l3 -> fpeq4 l1 l3.
Proof.
  now induction l1 as [| h1 t1]; fpeq4.
Qed.

#[global] Hint Resolve fpeq4_refl fpeq4_sym fpeq4_trans : core.

Lemma Proper_nel_app :
  forall (X Y : Sgr) (l1 l1' l2 l2' : nel (X + Y)),
    fpeq4 l1 l1' -> fpeq4 l2 l2' -> fpeq4 (nel_app l1 l2) (nel_app l1' l2').
Proof.
Admitted.

Lemma equiv_nel_normalize :
  forall (X Y : Sgr) (l1 l2 : nel (X + Y)),
    equiv_nel (normalize l1) (normalize l2) <-> equiv_nel l1 l2.
Proof.
Admitted.

#[export]
Instance Sgr_freeprod_setoid (X Y : Sgr) : Setoid' :=
{
  carrier := nel (X + Y);
  setoid := Setoid_kernel_equiv
    (@CoqSetoid_nel (CoqSetoid_coproduct X Y)) (@normalize X Y)
}.

Definition Sgr_freeprod_setoid_finl
  (X Y : Sgr) : SetoidHom X (Sgr_freeprod_setoid X Y).
Proof.
  now exists (fun x : X => singl (inl x)).
Defined.

Definition Sgr_freeprod_setoid_finr
  (X Y : Sgr) : SetoidHom Y (Sgr_freeprod_setoid X Y).
Proof.
  now exists (fun y : Y => singl (inr y)).
Defined.

#[refine]
#[export]
Instance Sgr_freeprod (X Y : Sgr) : Sgr :=
{
  setoid := Sgr_freeprod_setoid X Y;
  op := nel_app
}.
Proof.
  - intros l1 l1' H1 l2 l2' H2. cbn in *. destruct cheat.
  - destruct cheat.
Defined.

Definition Sgr_finl (X Y : Sgr) : SgrHom X (Sgr_freeprod X Y).
Proof.
  now exists (Sgr_freeprod_setoid_finl X Y); cbn.
Defined.

Definition Sgr_finr (X Y : Sgr) : SgrHom Y (Sgr_freeprod X Y).
Proof.
  now exists (Sgr_freeprod_setoid_finr X Y); cbn.
Defined.

Fixpoint freemap {X Y A : Sgr} (f : SgrHom X A) (g : SgrHom Y A) (l : nel (X + Y)) : nel A :=
match l with
| singl (inl x) => singl (f x)
| singl (inr y) => singl (g y)
| inl x ::: t => f x ::: freemap f g t
| inr y ::: t => g y ::: freemap f g t
end.

Fixpoint fold {A : Sgr} (l : nel A) : A :=
match l with
| singl a => a
| a ::: singl a' => op a a'
| a ::: t => op a (fold t)
end.

Lemma Proper_fold :
  forall (A : Sgr) (l1 l2 : nel A),
    equiv_nel l1 l2 -> fold l1 == fold l2.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; cat.
  destruct t1, t2; cbn in *.
    rewrite H, H0.
Abort.

Definition Sgr_setoid_copair
  (X Y A : Sgr) (f : SgrHom X A) (g : SgrHom Y A) : SetoidHom (Sgr_freeprod X Y) A.
Proof.
  exists (fun l => fold (freemap f g l)).
  intros l1 l2 Heq; cbn in *; revert l2 Heq.
  induction l1 as [[x | y] | [x | y] t1]; cbn.
Admitted.

Definition Sgr_copair (X Y A : Sgr) (f : SgrHom X A) (g : SgrHom Y A)
    : SgrHom (Sgr_freeprod X Y) A.
Proof.
Admitted.
*)