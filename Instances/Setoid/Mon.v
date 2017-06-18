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

Coercion sgr : Mon >-> Sgr.

Hint Resolve neutr_l neutr_r.

Ltac mon_simpl := intros;
match goal with
  (* Neutral element of the operation. Not sure if works. *)
  | H : context [?op neutr _] |- _ => rewrite neutr_l in H
  | H : context [?op _ neutr] |- _ => rewrite neutr_r in H
  | |- context [?op neutr _] => rewrite neutr_l
  | |- context [?op _ neutr] => rewrite neutr_r
  | f : ?X -> ?Y, X_neutr : ?X, pres_neutr : ?f ?X_neutr == ?neutr2 |- _ =>
    match goal with
      (* This can't be here because H gets rewritten in itself and thus
         effectively destroyed. *)
      (*| H : context [f ?neutr1] |- _ => rewrite pres_neutr in H*)
      | |- context [?f ?neutr1] => rewrite pres_neutr
    end
  (* Homomorphisms *)
  | f : ?X -> ?Y, H : ?f neutr == neutr |- context [?f neutr] =>
    rewrite H
  | _ => idtac
end; sgr_simpl.

Ltac mon_simpl2 := intros;
match goal with
  | X_neutr : ?X |- _ => match goal with
    | op : X -> ?Y |- _ => clear
  end
end.

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

Definition MonHom (X Y : Mon) : Type :=
    {f : SgrHom X Y | f neutr == neutr}.

Definition MonHom_SgrHom (X Y : Mon) (f : MonHom X Y)
    : SgrHom X Y := proj1_sig f.
Coercion MonHom_SgrHom : MonHom >-> SgrHom.

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

Ltac mon_aux :=
match goal with
  | |- (_, _) = _ => f_equal
  | _ => cat
end.

Ltac mon_wut := repeat (mon_simpl || monobs || monhoms || mon_aux || cat).
Ltac mon := try (mon_wut; fail).

Ltac mon_wut' := repeat (mon_simpl || monobs' || monhoms' || mon_aux || cat).
Ltac mon' := try (mon_wut'; fail).

Inductive exp : Mon -> Type :=
    | Id : forall X : Mon, exp X
    | Var : forall X : Mon, X -> exp X
    | Op : forall X : Mon, exp X -> exp X -> exp X
    | Mor : forall X Y : Mon, MonHom X Y -> exp X -> exp Y.

Arguments Id [X].
Arguments Var [X] _.
Arguments Op [X] _ _.
Arguments Mor [X Y] _ _ .

Fixpoint expDenote {X : Mon} (e : exp X) : X :=
match e with
    | Id => neutr
    | Var v => v
    | Op e1 e2 => op (expDenote e1) (expDenote e2)
    | Mor f e' => f (expDenote e')
end.

Require Import List.
Import ListNotations.

Fixpoint expDenoteL {X : Mon} (l : list X) : X :=
match l with
    | [] => neutr
    | h :: t => op h (expDenoteL t)
end.

Fixpoint flatten {X : Mon} (e : exp X) : list X :=
match e with
    | Id => []
    | Var v => [v]
    | Op e1 e2 => flatten e1 ++ flatten e2
    | Mor f Id => []
    | Mor f e' => map f (flatten e')
end.

Lemma flatten_Hom : forall (X : Mon) (f : MonHom X X) (e : exp X),
  e <> Id -> flatten (Mor f e) = map f (flatten e).
Proof.
  destruct e; auto.
Qed.

Lemma expDenoteL_app :
  forall (X : Mon) (l1 l2 : list X),
    expDenoteL (l1 ++ l2) == op (expDenoteL l1) (expDenoteL l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    rewrite neutr_l. reflexivity.
    rewrite <- assoc. apply op_Proper.
      reflexivity.
      rewrite IHt1. reflexivity.
Qed.

Lemma expDenoteL_hom :
  forall (X Y : Mon) (f : MonHom X Y) (l : list X),
    expDenoteL (map f l) == f (expDenoteL l).
Proof.
  induction l as [| h t]; simpl.
    mon'.
    assert (f (op h (expDenoteL t)) == op (f h) (f (expDenoteL t))).
      mon'.
      rewrite H. apply op_Proper.
        reflexivity.
        assumption.
Qed.

Theorem flatten_correct :
  forall (X : Mon) (e : exp X),
    expDenoteL (flatten e) == expDenote e.
Proof.
  induction e.
    reflexivity.
    mon.
    simpl. rewrite expDenoteL_app. apply op_Proper; assumption.
    destruct e; simpl.
      mon'.
      mon'.
      rewrite expDenoteL_hom. monhom' m. mon'.
      rewrite expDenoteL_hom. mon'.
Qed.

Theorem mon_reflect :
  forall (X : Mon) (e1 e2 : exp X),
    expDenoteL (flatten e1) == expDenoteL (flatten e2) ->
      expDenote e1 == expDenote e2.
Proof.
  induction e1; intros; repeat rewrite flatten_correct in H;
  assumption.
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

Ltac mon2 := simpl; intros;
match goal with
    | |- ?e1 == ?e2 =>
        let e1' := reify e1 in
        let e2' := reify e2 in
          change (expDenote e1' == expDenote e2');
          apply mon_reflect; simpl
end.

Ltac mon2' := mon2; try reflexivity.

Goal forall (X : Mon) (a b c : X),
  op a (op b c) == op (op a b) c.
Proof.
  mon2'.
Qed.

Goal forall (X : Mon) (f : MonHom X X) (a b : X),
  f (op a b) == op (f a) (f b).
Proof.
  mon2'.
Qed.

Goal forall (X : Mon) (f : MonHom X X) (a b c : X),
  op (f (f neutr)) (op (f a) (f (op b c))) ==
  op (f a) (op (f b) (f c)).
Proof.
  mon2'.
Qed.

Goal forall (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z),
  g (f neutr) == neutr.
Proof. mon2'.
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
  red. exists (SgrComp f g). Time mon2'.
Defined.

Definition MonId (X : Mon) : MonHom X X.
Proof. red. exists (SgrId X). Time mon2'. Defined.

Instance MonCat : Cat :=
{
    Ob := Mon;
    Hom := MonHom;
    HomSetoid := MonHomSetoid;
    comp := MonComp;
    id := MonId
}.
Proof.
  (* Proper *) proper. mon'.
  (* Category laws *) Time all: mon'.
Defined.

Instance Mon_init : Mon :=
{
    sgr := Sgr_term;
    neutr := tt
}.
Proof. all: mon. Defined.

Definition Mon_Sgr_create (X : Mon) : SgrHom Mon_init X.
Proof.
  Definition Mon_Setoid_create (X : Mon) : SetoidHom Mon_init X.
  Proof.
    red. exists (fun _ => neutr). proper.
  Defined.
  red. exists (Mon_Setoid_create X). Time mon2'.
Defined.

Definition Mon_create (X : Mon) : Hom Mon_init X.
Proof.
  mon_simpl. exists (Mon_Sgr_create X). mon2'.
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

Definition Mon_Sgr_delete (X : Mon) : SgrHom X Mon_term.
Proof.
  Definition Mon_Setoid_delete (X : Mon) : SetoidHom X Mon_term.
  Proof.
    red. exists (fun _ => tt). proper.
  Defined.
  red. exists (Mon_Setoid_delete X). mon.
Defined.

Definition Mon_delete (X : Mon) : Hom X Mon_term.
Proof.
  mon_simpl. exists (Mon_Sgr_delete X). mon.
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
  red. exists (Sgr_fpair f g). mon.
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
  repeat red. intros. mon.
Defined.