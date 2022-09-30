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

Fixpoint expDenoteNel {X : Sgr} (l : Nel X) : X :=
match tl l with
| None => hd l
| Some t => op (hd l) (expDenoteNel t)
end.

Lemma expDenoteNel_napp :
  forall (X : Sgr) (l1 l2 : Nel X),
    expDenoteNel (napp l1 l2) == op (expDenoteNel l1) (expDenoteNel l2).
Proof.
  induction l1 as [| h1 t1] using Nel_ind'; cbn; intros; [easy |].
  now rewrite IHt1, assoc.
Qed.

Lemma expDenoteNel_hom :
  forall (X Y : Sgr) (f : SgrHom X Y) (l : Nel X),
    expDenoteNel (nmap f l) == f (expDenoteNel l).
Proof.
  induction l as [| h t] using Nel_ind'; cbn; [easy |].
  now rewrite pres_op, IHt.
Qed.

Fixpoint flatten {X : Sgr} (e : exp X) : Nel X :=
match e with
| Var v => Cons v None
| Op e1 e2 => napp (flatten e1) (flatten e2)
| Mor f e' => nmap f (flatten e')
end.

Lemma flatten_correct :
  forall (X : Sgr) (e : exp X),
    expDenoteNel (flatten e) == expDenote e.
Proof.
  induction e; cbn; [easy | |].
  - now rewrite expDenoteNel_napp, IHe1, IHe2.
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

Inductive SCE {A B : Sgr} : Nel (A + B) -> Nel (A + B) -> Prop :=
| SCE_refl :
  forall l : Nel (A + B), SCE l l
| SCE_sym :
  forall l1 l2 : Nel (A + B),
    SCE l1 l2 -> SCE l2 l1
| SCE_trans :
  forall l1 l2 l3 : Nel (A + B),
    SCE l1 l2 -> SCE l2 l3 -> SCE l1 l3
| SCE_hd :
  forall {h1 h2 : A + B}, h1 == h2 -> SCE (Cons h1 None) (Cons h2 None)
| SCE_cons :
  forall {h1 h2 : A + B} {t1 t2 : Nel (A + B)},
    h1 == h2 -> SCE t1 t2 -> SCE (Cons h1 (Some t1)) (Cons h2 (Some t2))
| SCE_cons_op_l :
  forall (a1 a2 : A) (t : option (Nel (A + B))),
    SCE (Cons (inl a1) (Some (Cons (inl a2) t))) (Cons (inl (op a1 a2)) t)
| SCE_cons_op_r :
  forall (b1 b2 : B) (t : option (Nel (A + B))),
    SCE (Cons (inr b1) (Some (Cons (inr b2) t))) (Cons (inr (op b1 b2)) t).

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
  forall (A B : Sgr) (l l1 l2 : Nel (A + B)),
    SCE l1 l2 -> SCE (napp l l1) (napp l l2).
Proof.
  induction l as [h | h t] using Nel_ind'; cbn; intros.
  - now apply SCE_cons.
  - now apply SCE_cons; [| apply IHt].
Qed.

Lemma SCE_app :
  forall {A B : Sgr} (l11 l12 l21 l22 : Nel (A + B)),
    SCE l11 l12 -> SCE l21 l22 -> SCE (napp l11 l21) (napp l12 l22).
Proof.
  intros * H1 H2; revert l21 l22 H2.
  induction H1; cbn; intros.
  - now apply SCE_app_l.
  - now eauto.
  - now eauto.
  - now eauto.
  - now eauto.
  - rewrite SCE_cons_op_l.
    now destruct t; apply SCE_cons; [| apply SCE_app_l | |].
  - rewrite SCE_cons_op_r.
    now destruct t; apply SCE_cons; [| apply SCE_app_l | |].
Defined.

#[export]
Instance Sgr_coproduct_Setoid' (A B : Sgr) : Setoid' :=
{
  carrier := Nel (A + B);
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
  op := fun l1 l2 => napp l1 l2;
}.
Proof.
  - intros l1 l1' H1 l2 l2' H2; cbn in *.
    now apply SCE_app.
  - now cbn; intros; rewrite napp_assoc.
Defined.

#[export]
Instance Sgr_finl' (A B : Sgr) : SetoidHom A (Sgr_coproduct A B).
Proof.
  esplit. Unshelve. all: cycle 1.
  - exact (fun a => Cons (inl a) None).
  - now constructor.
Defined.

#[export]
Instance Sgr_finl (A B : Sgr) : SgrHom A (Sgr_coproduct A B).
Proof.
  esplit with (Sgr_finl' A B); cbn.
  now intros; rewrite SCE_cons_op_l.
Defined.

#[export]
Instance Sgr_finr' (A B : Sgr) : SetoidHom B (Sgr_coproduct A B).
Proof.
  esplit. Unshelve. all: cycle 1.
  - exact (fun b => Cons (inr b) None).
  - now constructor.
Defined.

#[export]
Instance Sgr_finr (A B : Sgr) : SgrHom B (Sgr_coproduct A B).
Proof.
  esplit with (Sgr_finr' A B); cbn.
  now intros; rewrite SCE_cons_op_r.
Defined.

Fixpoint Sgr_copair'
  {A B X : Sgr} (f : SgrHom A X) (g : SgrHom B X) (l : Nel (A + B)) : X :=
match tl l with
| None =>
  match hd l with
  | inl a => f a
  | inr b => g b
  end
| Some t =>
  match hd l with
  | inl a => op (f a) (Sgr_copair' f g t)
  | inr b => op (g b) (Sgr_copair' f g t)
  end
end.

Lemma Sgr_copair'_app :
  forall {A B X : Sgr} (f : SgrHom A X) (g : SgrHom B X) (l1 l2 : Nel (A + B)),
    Sgr_copair' f g (napp l1 l2) == op (Sgr_copair' f g l1) (Sgr_copair' f g l2).
Proof.
  now induction l1 as [[] | [] t] using Nel_ind'; cbn; intros; rewrite ?IHt, ?assoc.
Qed.

#[export]
Instance Sgr_copair_Setoid'
  {A B X : Sgr} (f : SgrHom A X) (g : SgrHom B X) : SetoidHom (Sgr_coproduct A B) X.
Proof.
  esplit with (Sgr_copair' f g).
  intros l1 l2 Heq; cbn in *.
  induction Heq; cbn.
  - easy.
  - easy.
  - now rewrite IHHeq1, IHHeq2.
  - destruct h1, h2; cbn in *; [| easy | easy |].
    + now rewrite H.
    + now rewrite H.
  - destruct h1, h2; cbn in *; [| easy | easy |].
    + now rewrite H, IHHeq.
    + now rewrite H, IHHeq.
  - now destruct t as [t |]; rewrite pres_op, ?assoc.
  - now destruct t as [t |]; rewrite pres_op, ?assoc.
Defined.

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
    induction l as [[a | b] | h t] using Nel_ind'; cbn.
    + now apply HA.
    + now apply HB.
    + change {| hd := h; tl := Some t; |} with (@op (Sgr_coproduct A B) (Cons h None) t).
      now rewrite (@pres_op _ _ h1), (@pres_op _ _ h2), IHt; destruct h; rewrite ?HA, ?HB.
Defined.

#[refine]
#[export]
Instance Sgr_equalizer {A B : Sgr} (f g : SgrHom A B) : Sgr :=
{
  setoid := CoqSetoid_equalizer f g;
}.
Proof.
  - cbn; intros [x Hx] [y Hy].
    exists (op x y).
    now rewrite !pres_op, Hx, Hy.
  - intros [a1 H1] [a2 H2] Heq1 [a3 H3] [a4 H4] Heq2; cbn in *.
    now rewrite Heq1, Heq2.
  - intros [x Hx] [y Hy] [z Hz]; cbn in *.
    now rewrite assoc.
Defined.

#[refine]
#[export]
Instance Sgr_equalize {A B : Sgr} (f g : SgrHom A B) : SgrHom (Sgr_equalizer f g) A :=
{
  setoidHom := CoqSetoid_equalize f g;
}.
Proof.
  now intros [x Hx] [y Hy]; cbn.
Defined.

#[export]
#[refine]
Instance Sgr_factorize
  {A B : Sgr} {f g : SgrHom A B}
  {E' : Sgr} (e' : Hom E' A) (Heq : (e' .> f) == (e' .> g))
  : SgrHom E' (Sgr_equalizer f g) :=
{
  setoidHom := CoqSetoid_factorize e' Heq;
}.
Proof.
  now cbn; intros; rewrite pres_op.
Defined.

#[refine]
#[export]
Instance HasEqualizers_Sgr : HasEqualizers SgrCat :=
{
  equalizer := @Sgr_equalizer;
  equalize := @Sgr_equalize;
  factorize := @Sgr_factorize;
}.
Proof.
  split; cbn.
  - now intros [x H]; cbn.
  - easy.
  - easy.
Defined.

Inductive Sgr_coeq_equiv {A B : Sgr} (f g : SgrHom A B) : B -> B -> Prop :=
| SgrCE_quot : forall a : A, Sgr_coeq_equiv f g (f a) (g a)
| SgrCE_op   :
  forall {l1 r1 l2 r2 : B},
    Sgr_coeq_equiv f g l1 l2 ->
    Sgr_coeq_equiv f g r1 r2 ->
      Sgr_coeq_equiv f g (op l1 r1) (op l2 r2)
| SgrCE_refl : forall {b1 b2 : B}, b1 == b2 -> Sgr_coeq_equiv f g b1 b2
| SgrCE_sym  :
  forall {b1 b2 : B}, Sgr_coeq_equiv f g b1 b2 -> Sgr_coeq_equiv f g b2 b1
| SgrCE_trans :
  forall {b1 b2 b3 : B},
    Sgr_coeq_equiv f g b1 b2 ->
    Sgr_coeq_equiv f g b2 b3 ->
      Sgr_coeq_equiv f g b1 b3.

#[export] Hint Constructors Sgr_coeq_equiv : core.

#[refine]
#[export]
Instance Sgr_coequalizer_Setoid {A B : Sgr} (f g : SgrHom A B) : Setoid' :=
{
  carrier := B;
  Setoids.setoid :=
  {|
    equiv := Sgr_coeq_equiv f g;
  |};
}.
Proof.
  split; red.
  - now constructor.
  - now apply SgrCE_sym.
  - now intros; apply SgrCE_trans with y.
Defined.

#[refine]
#[export]
Instance Sgr_coequalizer {A B : Sgr} (f g : SgrHom A B) : Sgr :=
{
  setoid := Sgr_coequalizer_Setoid f g;
  op := op;
}.
Proof.
  - intros x1 x2 H12 x3 x4 H34; cbn in *.
    now constructor.
  - cbn; intros.
    apply SgrCE_refl.
    now rewrite assoc.
Defined.

#[refine]
#[export]
Instance Sgr_coequalize' {A B : Sgr} (f g : SgrHom A B) : SetoidHom B (Sgr_coequalizer f g) :=
{
  func := fun b => b;
}.
Proof.
  intros b1 b2 Heq; cbn.
  now constructor.
Defined.

#[refine]
#[export]
Instance Sgr_coequalize {A B : Sgr} (f g : SgrHom A B) : SgrHom B (Sgr_coequalizer f g) :=
{
  setoidHom := Sgr_coequalize' f g;
}.
Proof.
  now constructor; cbn.
Defined.

#[export]
#[refine]
Instance Sgr_cofactorize'
  {A B : Sgr} {f g : Hom A B}
  {Q : Sgr} (q : Hom B Q) (Heq : f .> q == g .> q)
  : SetoidHom (Sgr_coequalizer f g) Q :=
{
  func := q;
}.
Proof.
  intros x y H. cbn in *.
  induction H.
  - easy.
  - now rewrite !pres_op, IHSgr_coeq_equiv1, IHSgr_coeq_equiv2.
  - now rewrite H.
  - now symmetry.
  - now transitivity (q b2).
Defined.

#[export]
#[refine]
Instance Sgr_cofactorize
  {A B : Sgr} {f g : Hom A B}
  {Q : Sgr} (q : Hom B Q) (Heq : f .> q == g .> q)
  : SgrHom (Sgr_coequalizer f g) Q :=
{
  setoidHom := Sgr_cofactorize' Heq;
}.
Proof.
  now cbn; intros; rewrite pres_op.
Defined.

#[refine]
#[export]
Instance HasCoequalizers_Sgr : HasCoequalizers SgrCat :=
{
  coequalizer := @Sgr_coequalizer;
  coequalize := @Sgr_coequalize;
  cofactorize := @Sgr_cofactorize;
}.
Proof.
  split; cbn.
  - now constructor.
  - easy.
  - easy.
Defined.