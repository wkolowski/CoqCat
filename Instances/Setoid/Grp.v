From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Zero Product Coproduct.
From Cat.Instances Require Import Setoids Setoid.Mon.

Require Import List.
Import ListNotations.

Set Implicit Arguments.

Class Grp : Type :=
{
  mon :> Mon;
  inv : SetoidHom mon mon;
  inv_l : forall x : mon, op (inv x) x == neutr;
  inv_r : forall x : mon, op x (inv x) == neutr
}.

#[global] Hint Resolve inv_l inv_r : core.

Coercion mon : Grp >-> Mon.

Lemma inv_involutive :
  forall (G : Grp) (g : G),
    inv (inv g) == g.
Proof.
  now intros; rewrite <- neutr_l, <- (inv_l (inv g)), <- assoc, inv_l, neutr_r.
Qed.

Lemma neutr_unique_l :
  forall (G : Grp) (e : G),
    (forall g : G, op e g == g) -> e == neutr.
Proof.
  now intros; rewrite <- (neutr_r e), H.
Defined.

Lemma neutr_unique_r :
  forall (G : Grp) (e : G),
    (forall g : G, op g e == g) -> e == neutr.
Proof.
  now intros; rewrite <- (neutr_l e), H.
Defined.

Lemma inv_op :
  forall (G : Grp) (a b : G),
    inv (op a b) == op (inv b) (inv a).
Proof.
  intros G a b.
  assert (forall x y : G, op (op x y) (inv (op x y)) == neutr) by easy.
  assert (forall x y : G, op (op x y) (op (inv y) (inv x)) == neutr)
    by now intros; rewrite <- assoc, (assoc y _), inv_r, neutr_l.
  assert (op (op a b) (inv (op a b)) == op (op a b) (op (inv b) (inv a)))
    by now rewrite H, H0.
  assert (op (inv (op a b)) (op (op a b) (inv (op a b)))
            ==
          op (inv (op a b)) (op (op a b) (op (inv b) (inv a))))
    by now rewrite H1.
  now repeat (rewrite assoc, inv_l, neutr_l in H2).
Defined.

Lemma inv_neutr :
  forall G : Grp,
    inv neutr == neutr.
Proof.
  now intros; rewrite <- (neutr_l (inv neutr)), inv_r.
Defined.

#[global] Hint Resolve inv_involutive neutr_unique_l neutr_unique_r inv_op inv_neutr : core.

Class GrpHom (X Y : Grp) : Type :=
{
  monHom :> MonHom X Y;
  pres_inv : forall x : X, monHom (inv x) == inv (monHom x)
}.

Coercion monHom : GrpHom >-> MonHom.

Inductive exp (X : Grp) : Type :=
| Id : exp X
| Var : X -> exp X
| Op : exp X -> exp X -> exp X
| Mor : forall A : Grp, GrpHom A X -> exp A -> exp X
| Inv : exp X -> exp X.

Arguments Id  {X}.
Arguments Var {X} _.
Arguments Op  {X} _ _.
Arguments Mor {X A} _ _.
Arguments Inv {X} _.

Fixpoint expDenote {X : Grp} (e : exp X) : X :=
match e with
| Id => neutr
| Var v => v
| Op e1 e2 => op (expDenote e1) (expDenote e2)
| Mor f e' => f (expDenote e')
| Inv e' => inv (expDenote e')
end.

Fixpoint simplify {X : Grp} (e : exp X) : exp X :=
match e with
| Id => Id
| Var v => Var v
| Op e1 e2 => Op (simplify e1) (simplify e2)
| Mor f e' =>
  match simplify e' with
  | Id => Id
  | Op e1 e2 => Op (Mor f e1) (Mor f e2)
  | Inv e'' => Inv (Mor f e'')
  | e'' => Mor f e''
  end
| Inv e' =>
  match simplify e' with
  | Id => Id
  | Op e1 e2 => Op (Inv e2) (Inv e1)
  | Inv e'' => e''
  | e'' => Inv e''
  end
end.

Lemma simplify_correct :
  forall (X : Grp) (e : exp X),
    expDenote (simplify e) == expDenote e.
Proof.
  induction e; cbn; [easy | easy | | |].
  - now rewrite IHe1, IHe2.
  - now destruct (simplify e); cbn in *; rewrite <- IHe, ?pres_neutr, ?pres_op, ?pres_inv.
  - now destruct (simplify e); cbn in *; rewrite <- IHe, ?inv_neutr, ?inv_op, ?inv_involutive.
Qed.

Fixpoint expDenoteL {X : Grp} (l : list X) : X :=
match l with
| [] => neutr
| h :: t => op h (expDenoteL t)
end.

Lemma expDenoteL_app :
  forall (X : Grp) (l1 l2 : list X),
    expDenoteL (l1 ++ l2) == op (expDenoteL l1) (expDenoteL l2).
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
  - now rewrite neutr_l.
  - now rewrite <- assoc, IHt1.
Qed.

Lemma expDenoteL_hom :
  forall (X Y : Grp) (f : MonHom X Y) (l : list X),
    expDenoteL (map f l) == f (expDenoteL l).
Proof.
  induction l as [| h t]; cbn.
  - now rewrite pres_neutr.
  - now rewrite pres_op, IHt.
Qed.

Lemma expDenoteL_inv :
  forall (X : Grp) (l : list X),
    expDenoteL (map inv l) == inv (expDenoteL (rev l)).
Proof.
  induction l as [| h t]; cbn.
  - now rewrite inv_neutr.
  - now rewrite expDenoteL_app, inv_op; cbn; rewrite neutr_r, IHt.
Qed.

Fixpoint flatten {X : Grp} (e : exp X) : list X :=
match e with
| Id => []
| Var v => [v]
| Op e1 e2 => flatten e1 ++ flatten e2
| Mor f e' => map f (flatten e')
| Inv e' => rev (map inv (flatten e'))
end.

Lemma flatten_correct :
  forall (X : Grp) (e : exp X),
    expDenoteL (flatten e) == expDenote e.
Proof.
  induction e; cbn; [easy | | | |].
  - now rewrite neutr_r.
  - now rewrite expDenoteL_app, IHe1, IHe2.
  - now rewrite expDenoteL_hom, IHe.
  - now rewrite <- map_rev, expDenoteL_inv, rev_involutive, IHe.
Qed.

Lemma grp_reflect :
  forall (X : Grp) (e1 e2 : exp X),
    expDenoteL (flatten (simplify e1)) ==
    expDenoteL (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  now intros; rewrite !flatten_correct, !simplify_correct in H.
Qed.

Lemma grp_reflect2 :
  forall (X : Grp) (e1 e2 : exp X),
    expDenoteL (flatten (simplify (simplify e1))) ==
    expDenoteL (flatten (simplify (simplify e2))) ->
      expDenote e1 == expDenote e2.
Proof.
  now intros; rewrite !flatten_correct, !simplify_correct in H.
Qed.

Class Reify (X : Grp) (x : X) : Type :=
{
  reify : exp X;
  reify_spec : expDenote reify == x
}.

Arguments Reify {X} _.
Arguments reify {X} _ {Reify}.

#[refine]
#[export]
Instance ReifyVar (X : Grp) (x : X) : Reify x | 1 :=
{
  reify := Var x
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance ReifyOp (X : Grp) (a b : X) (Ra : Reify a) (Rb : Reify b) : Reify (@op X a b) | 0 :=
{
  reify := Op (reify a) (reify b)
}.
Proof.
  now cbn; rewrite !reify_spec.
Defined.

#[refine]
#[export]
Instance ReifyHom (X Y : Grp) (f : GrpHom X Y) (x : X) (Rx : Reify x) : Reify (f x) | 0 :=
{
  reify := Mor f (reify x)
}.
Proof.
  now cbn; rewrite reify_spec.
Defined.

#[refine]
#[export]
Instance ReifyId (X : Grp) : Reify neutr | 0 :=
{
  reify := Id
}.
Proof.
  easy.
Defined.

#[refine]
#[export]
Instance ReifyInv (X : Grp) (x : X) (Rx : Reify x) : Reify (inv x) :=
{
  reify := Inv (reify x)
}.
Proof.
  now cbn; rewrite reify_spec.
Defined.

Ltac reflect_grp := cbn; intros;
match goal with
| |- ?e1 == ?e2 =>
  change (expDenote (reify e1) == expDenote (reify e2));
  apply grp_reflect2; cbn
end.

Ltac grp_simpl := mon_simpl. 

Ltac grpob G := try intros until G;
match type of G with
| Grp =>
  let a := fresh G "_inv" in 
  let b := fresh G "_inv_l" in
  let c := fresh G "_inv_r" in destruct G as [G a b c]
| Ob _ => progress cbn in G; grpob G
end.

Ltac grpob' G := grpob G; monob' G.

Ltac grpobs_template tac := repeat
match goal with
| G : Grp |- _ => tac G
| G : Ob _ |- _ => tac G
end.

Ltac grpobs := grpobs_template grpob.
Ltac grpobs' := grpobs_template grpob'.

Ltac grphom f :=
match type of f with
| GrpHom _ _ =>
  let a := fresh f "_pres_inv" in destruct f as [f a]
| Hom _ _ => progress cbn in f; grphom f
end; cbn in *.

Ltac grphom' f := grphom f; monhom' f.

Ltac grphoms_template tac := intros; repeat
match goal with
| f : GrpHom _ _ |- _ => tac f
| f : Hom _ _ |- _ => tac f
end; grp_simpl.

Ltac grphoms := grphoms_template grphom.
Ltac grphoms' := grphoms_template grphom'.

Ltac grp := intros; try (cat; fail); repeat
match goal with
| |- _ == _ => now reflect_grp
| |- Equivalence _ => solve_equiv
| |- Proper _ _ => proper
(*| |- (_, _) = (_, _) => f_equal*)
| _ => grp_simpl || grpobs' || grphoms' || cat
end.

Section test.

Variables X Y Z : Grp.

Variables x x' a b c : X.
Variables y y' : Y.
Variables z z' : Z.

Variable f : GrpHom X Y.
Variable g : GrpHom Y Z.
Variable h : GrpHom X X.

(** Associativity *)
Goal op a (op b c) == op (op a b) c.
Proof.
  now reflect_grp.
Qed.

(** Homomorphism *)
Goal f (op a b) == op (f a) (f b).
Proof.
  now reflect_grp.
Qed.

(** Neutral element *)
Goal f neutr == neutr.
Proof.
  now reflect_grp.
Qed.

Goal
  op (h (h neutr)) (op (h a) (h (op b c))) ==
  op (h a) (op (h b) (h c)).
Proof.
  now reflect_grp.
Qed.

Goal inv (op a b) == op (inv b) (inv a).
Proof.
  now reflect_grp.
Qed.

Goal inv (inv a) == a.
Proof.
  now reflect_grp.
Qed.

Goal f (inv (op a b)) == op (inv (f b)) (inv (f a)).
Proof.
  now reflect_grp.
Qed.

End test.

#[refine]
#[export]
Instance GrpHomSetoid (X Y : Grp) : Setoid (GrpHom X Y) :=
{
  equiv := fun f g : GrpHom X Y => @equiv _ (SgrHomSetoid X Y) f g
}.
Proof. now apply Setoid_kernel_equiv. Defined.

Definition GrpComp (X Y Z : Grp) (f : GrpHom X Y) (g : GrpHom Y Z) : GrpHom X Z.
Proof.
  exists (MonComp f g); cbn.
  now intros; rewrite !pres_inv.
Defined.

Definition GrpId (X : Grp) : GrpHom X X.
Proof.
  now exists (MonId X).
Defined.

#[refine]
#[export]
Instance GrpCat : Cat :=
{
  Ob := Grp;
  Hom := GrpHom;
  HomSetoid := GrpHomSetoid;
  comp := GrpComp;
  id := GrpId;
}.
Proof.
  - intros A B C f1 f2 Hf g1 g2 Hg x; cbn in *.
    now rewrite Hf, Hg.
  - now grp.
  - now grp.
  - now grp.
Defined.

Definition Grp_zero_inv : SetoidHom Mon_init Mon_init.
Proof.
  now exists (fun _ => tt).
Defined.

#[refine]
#[export]
Instance Grp_zero : Grp :=
{
  mon := Mon_init;
  inv := Grp_zero_inv
}.
Proof. all: now grp. Defined.

Definition Grp_create (X : Grp) : Hom Grp_zero X.
Proof.
  exists (Mon_create X); cbn.
  now intros; rewrite inv_neutr.
Defined.

#[refine]
#[export]
Instance HasInit_Grp : HasInit GrpCat :=
{
    init := Grp_zero;
    create := Grp_create
}.
Proof. now grp. Defined.

Definition Grp_delete (X : Grp) : Hom X Grp_zero.
Proof.
  now exists (Mon_delete X).
Defined.

#[refine]
#[export]
Instance HasTerm_Grp : HasTerm GrpCat :=
{
  term := Grp_zero;
  delete := Grp_delete
}.
Proof. now grp. Defined.

#[refine]
#[export]
Instance HasZero_Grp : HasZero GrpCat :=
{
  HasInit_HasZero := HasInit_Grp;
  HasTerm_HasZero := HasTerm_Grp
}.
Proof. now grp. Defined.

Definition Grp_product_inv (X Y : Grp) : SetoidHom (Mon_product X Y) (Mon_product X Y).
Proof.
  exists (fun p : X * Y => (inv (fst p), inv (snd p))).
  intros [f1 Hf1] [f2 Hf2] Hf; cbn in *.
  now destruct Hf as [-> ->].
Defined.

#[refine]
#[export]
Instance Grp_product (X Y : Grp) : Grp :=
{
  mon := Mon_product X Y;
  inv := Grp_product_inv X Y
}.
Proof. all: now destruct x; grp. Defined.

Definition Grp_outl (X Y : Grp) : Hom (Grp_product X Y) X.
Proof.
  now exists (Mon_outl X Y).
Defined.

Definition Grp_outr (X Y : Grp) : Hom (Grp_product X Y) Y.
Proof.
  now exists (Mon_outr X Y).
Defined.

Definition Grp_fpair (A B X : Grp) (f : Hom X A) (g : Hom X B) : Hom X (Grp_product A B).
Proof.
  exists (Mon_fpair f g); cbn.
  now intros; rewrite !pres_inv.
Defined.

#[refine]
#[export]
Instance HasProducts_Grp : HasProducts GrpCat :=
{
  product := Grp_product;
  outl := Grp_outl;
  outr := Grp_outr;
  fpair := Grp_fpair
}.
Proof.
  split; cbn.
  - easy.
  - easy.
  - now split.
Defined.

Definition AutOb (C : Cat) (X : Ob C) : Type := unit.

Definition AutHom {C : Cat} {X : Ob C} (_ _ : AutOb C X) : Type := {f : Hom X X | isIso f}.

Definition AutHom_Fun
  {C : Cat} {X : Ob C} (A B : AutOb C X) (f : AutHom A B)
  : Hom X X := proj1_sig f.

Coercion AutHom_Fun : AutHom >-> Hom.

#[refine]
#[export]
Instance AutHomSetoid
  (C : Cat) (X : Ob C)
  : forall A B : AutOb C X, Setoid (AutHom A B) :=
{
  equiv := fun f g : AutHom A B => @equiv _ (@HomSetoid C X X) f g
}.
Proof. now grp. Defined.

Definition AutComp
  (C : Cat) (A : Ob C) (X Y Z : AutOb C A) (f : AutHom X Y) (g : AutHom Y Z) : AutHom X Z.
Proof.
  exists (f .> g).
  apply isIso_comp.
  - now destruct f.
  - now destruct g.
Defined.

Definition AutId (C : Cat) (A : Ob C) (X : AutOb C A) : AutHom X X.
Proof.
  exists (id A).
  now apply isAut_id.
Defined.

#[refine]
#[export]
Instance AutCat (C : Cat) (X : Ob C) : Cat :=
{
  Ob := AutOb C X;
  Hom := @AutHom C X;
  HomSetoid := @AutHomSetoid C X;
  comp := @AutComp C X;
  id := @AutId C X;
}.
Proof. all: now grp. Defined.