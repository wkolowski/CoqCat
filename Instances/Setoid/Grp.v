Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Logic.FunctionalExtensionality.

Require Export Cat.
Require Import Cat.Limits.InitTerm.
Require Import Cat.Limits.BinProdCoprod.

Require Export Cat.Instances.Setoid.Mon.

Set Implicit Arguments.

Class Grp : Type :=
{
    mon :> Mon;
    inv : SetoidHom mon mon;
    inv_l : forall x : mon, op (inv x) x == neutr;
    inv_r : forall x : mon, op x (inv x) == neutr
}.

Hint Resolve inv_l inv_r.

Coercion mon : Grp >-> Mon.

Theorem inv_involutive : forall (G : Grp) (g : G),
    inv (inv g) == g.
Proof.
  intros. pose (@op_Proper G).
  assert (op (inv (inv g)) (op (inv g) g) == g).
    rewrite assoc, inv_l, neutr_l. reflexivity.
    rewrite inv_l , neutr_r in H. assumption.
Qed.

Theorem neutr_unique_l : forall (G : Grp) (e : G),
    (forall g : G, op e g == g) -> e == neutr.
Proof.
  intros.
  assert (op e neutr == e). rewrite neutr_r. reflexivity.
  assert (op e neutr == neutr). apply H.
  rewrite H0 in H1. assumption.
Defined.

Theorem neutr_unique_r : forall (G : Grp) (e : G),
    (forall g : G, op g e == g) -> e == neutr.
Proof.
  intros.
  assert (op neutr e == e). rewrite neutr_l. reflexivity.
  assert (op neutr e == neutr). apply H. 
  rewrite H0 in H1. assumption.
Defined.

Theorem inv_op : forall (G : Grp) (a b : G),
    inv (op a b) == op (inv b) (inv a).
Proof.
  intros. pose (@op_Proper G).
  assert (forall x y : G, op (op x y) (inv (op x y)) == neutr). auto.
  assert (forall x y : G, op (op x y) (op (inv y) (inv x)) == neutr).
    intros. rewrite <- assoc. rewrite (assoc y _). rewrite inv_r.
    rewrite neutr_l. auto.
  assert (op (op a b) (inv (op a b)) == op (op a b) (op (inv b) (inv a))).
    rewrite H, H0. reflexivity.
  assert (op (inv (op a b)) (op (op a b) (inv (op a b))) ==
    op (inv (op a b)) (op (op a b) (op (inv b) (inv a)))).
    rewrite H1. reflexivity.
  repeat rewrite assoc, inv_l, neutr_l in H2. assumption.
Defined.

Theorem inv_neutr : forall (G : Grp), inv neutr == neutr.
Proof.
  intros.
  assert (op (inv neutr) neutr == neutr).
    rewrite inv_l. reflexivity.
  assert (op (inv neutr) neutr == inv neutr).
    rewrite neutr_r. reflexivity.
  rewrite <- H0, H. reflexivity.
Defined.

Hint Resolve inv_involutive neutr_unique_l neutr_unique_r inv_op inv_neutr.

Definition GrpHom (X Y : Grp) : Type := 
    {f : MonHom X Y | forall x : X, f (inv x) == inv (f x)}.

Definition GrpHom_MonHom (X Y : Grp) (f : GrpHom X Y)
    : MonHom X Y := proj1_sig f.
Coercion GrpHom_MonHom : GrpHom >-> MonHom.

Lemma inv_Proper : forall (X : Grp), Proper (equiv ==> equiv) inv.
Proof.
  unfold Proper, respectful; intros.
  destruct X, inv0; simpl in *. apply p. assumption.
Qed.

Inductive exp (X : Grp) : Type :=
    | Id : exp X
    | Var : X -> exp X
    | Op : exp X -> exp X -> exp X
    | Mor : forall A : Grp, GrpHom A X -> exp A -> exp X
    | Inv : exp X -> exp X.

Arguments Id [X].
Arguments Var [X] _.
Arguments Op [X] _ _.
Arguments Mor [X A] _ _.
Arguments Inv [X] _.

Fixpoint expDenote {X : Grp} (e : exp X) : X :=
match e with
    | Id => neutr
    | Var v => v
    | Op e1 e2 => op (expDenote e1) (expDenote e2)
    | Mor f e' => f (expDenote e')
    | Inv e' => inv (expDenote e')
end.

Require Import List.
Import ListNotations.

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

(* TODO *) Lemma MonHom_pres_neutr :
  forall (X Y : Mon) (f : MonHom X Y),
    f neutr == neutr.
Proof.
  destruct f; simpl. assumption.
Qed.

Lemma SgrHom_pres_op :
  forall (X Y : Sgr) (f : SgrHom X Y) (a b : X),
    f (op a b) == op (f a) (f b).
Proof.
  destruct f; simpl; intros. rewrite e. reflexivity.
Qed.

Lemma GrpHom_pres_inv :
  forall (X Y : Grp) (f : GrpHom X Y) (x : X),
    f (inv x) == inv (f x).
Proof.
  destruct f; simpl; intros. rewrite e. reflexivity.
Qed.

Theorem simplify_correct :
  forall (X : Grp) (e : exp X),
    expDenote (simplify e) == expDenote e.
Proof.
  induction e; simpl; pose (@op_Proper X); pose inv_Proper.
    reflexivity.
    reflexivity.
    rewrite IHe1, IHe2. reflexivity.
    destruct (simplify e); simpl in *; try pose (SgrHom_Proper g);
    rewrite <- IHe; try reflexivity.
      rewrite MonHom_pres_neutr. reflexivity.
      rewrite SgrHom_pres_op. reflexivity.
      rewrite GrpHom_pres_inv. reflexivity.
    destruct (simplify e); simpl in *; try pose (SgrHom_Proper g);
    try rewrite <- IHe.
      rewrite inv_neutr. reflexivity.
      reflexivity.
      rewrite inv_op. reflexivity.
      reflexivity.
      rewrite inv_involutive. reflexivity.
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
  induction l1 as [| h1 t1]; simpl; intros.
    rewrite neutr_l. reflexivity.
    rewrite <- assoc. apply op_Proper.
      reflexivity.
      rewrite IHt1. reflexivity.
Qed.

Lemma expDenoteL_hom :
  forall (X Y : Grp) (f : MonHom X Y) (l : list X),
    expDenoteL (map f l) == f (expDenoteL l).
Proof.
  induction l as [| h t]; simpl.
    rewrite MonHom_pres_neutr. reflexivity.
    rewrite SgrHom_pres_op. apply op_Proper; try rewrite IHt; reflexivity.
Qed.

Lemma expDenoteL_inv :
  forall (X : Grp) (l : list X),
    expDenoteL (map inv l) == inv (expDenoteL (rev l)).
Proof.
  induction l as [| h t]; simpl; pose (@op_Proper X); pose inv_Proper.
    rewrite inv_neutr. reflexivity.
    rewrite expDenoteL_app, inv_op; simpl. rewrite neutr_r.
      rewrite IHt. reflexivity.
Qed.

Fixpoint flatten {X : Grp} (e : exp X) : list X :=
match e with
    | Id => []
    | Var v => [v]
    | Op e1 e2 => flatten e1 ++ flatten e2
    | Mor f e' => map f (flatten e')
    | Inv e' => rev (map inv (flatten e'))
end.

Theorem flatten_correct :
  forall (X : Grp) (e : exp X),
    expDenoteL (flatten e) == expDenote e.
Proof.
  induction e; simpl; pose (@op_Proper X); try pose (SgrHom_Proper g).
    reflexivity.
    rewrite neutr_r. reflexivity.
    rewrite expDenoteL_app, IHe1, IHe2. reflexivity.
    rewrite expDenoteL_hom, IHe. reflexivity.
    rewrite <- map_rev, expDenoteL_inv, rev_involutive.
      apply inv_Proper. assumption.
Qed.

Theorem grp_reflect :
  forall (X : Grp) (e1 e2 : exp X),
    expDenoteL (flatten (simplify e1)) ==
    expDenoteL (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  intros.
  do 2 rewrite flatten_correct in H.
  do 2 rewrite simplify_correct in H.
  assumption.
Qed.

Theorem grp_reflect2 :
  forall (X : Grp) (e1 e2 : exp X),
    expDenoteL (flatten (simplify (simplify e1))) ==
    expDenoteL (flatten (simplify (simplify e2))) ->
      expDenote e1 == expDenote e2.
Proof.
  intros.
  do 2 rewrite flatten_correct in H.
  repeat rewrite simplify_correct in H.
  assumption.
Qed.

Ltac reify e :=
lazymatch e with
    | @neutr (@mon ?X) => constr:(@Id X)
    | op ?e1 ?e2 =>
        let e1' := reify e1 in
        let e2' := reify e2 in constr:(Op e1' e2')
    | SetoidHom_Fun (SgrHom_Fun (MonHom_SgrHom (GrpHom_MonHom ?f))) ?e =>
        let e' := reify e in constr:(Mor f e')
    | (SetoidHom_Fun inv) ?e =>
        let e' := reify e in constr:(Inv e')
    | ?v => constr:(Var v)
end.

Ltac reflect_grp := simpl; intros;
match goal with
    | |- ?e1 == ?e2 =>
        let e1' := reify e1 in
        let e2' := reify e2 in
          change (expDenote e1' == expDenote e2');
          apply grp_reflect2; simpl
end.

Ltac grp_simpl := mon_simpl. 

Ltac grpob G := try intros until G;
match type of G with
  | Grp =>
    let a := fresh G "_inv" in 
    let b := fresh G "_inv_l" in
    let c := fresh G "_inv_r" in destruct G as [G a b c]
  | Ob _ => progress simpl in G; grpob G
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
  | Hom _ _ => progress simpl in f; grphom f
end; simpl in *.

Ltac grphom' f := grphom f; monhom' f.

Ltac grphoms_template tac := intros; repeat
match goal with
  | f : GrpHom _ _ |- _ => tac f
  | f : Hom _ _ |- _ => tac f
end; grp_simpl.

Ltac grphoms := grphoms_template grphom.
Ltac grphoms' := grphoms_template grphom'.

Ltac grp := intros; try (reflect_grp; try reflexivity; fail); repeat
match goal with
    | |- _ == _ => reflect_grp; reflexivity
    | |- Equivalence _ => solve_equiv
    | |- Proper _ _ => proper
(*    | |- (_, _) = (_, _) => f_equal*)
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
  reflect_grp. reflexivity.
Qed.

(** Homomorphism *)
Goal f (op a b) == op (f a) (f b).
Proof.
  reflect_grp. reflexivity.
Qed.

(** Neutral element *)
Goal f neutr == neutr.
Proof.
  reflect_grp. reflexivity.
Qed.

Goal
  op (h (h neutr)) (op (h a) (h (op b c))) ==
  op (h a) (op (h b) (h c)).
Proof.
  reflect_grp. reflexivity.
Qed.

Goal inv (op a b) == op (inv b) (inv a).
Proof.
  reflect_grp. reflexivity.
Qed.

Goal inv (inv a) == a.
Proof.
  reflect_grp. reflexivity.
Qed.

Goal f (inv (op a b)) == op (inv (f b)) (inv (f a)).
Proof.
  reflect_grp. reflexivity.
Qed.

End test.

Instance GrpHomSetoid (X Y : Grp) : Setoid (GrpHom X Y) :=
{
  equiv := fun f g : GrpHom X Y =>
      @equiv _ (SgrHomSetoid X Y) (proj1_sig f) (proj1_sig g)
}.
Proof. apply Setoid_kernel_equiv. Defined.

Definition GrpComp (X Y Z : Grp) (f : GrpHom X Y) (g : GrpHom Y Z)
    : GrpHom X Z.
Proof.
  red. exists (MonComp f g). grp.
Defined.

Definition GrpId (X : Grp) : GrpHom X X.
Proof.
  red. exists (MonId X). grp.
Defined.

Instance GrpCat : Cat :=
{
    Ob := Grp;
    Hom := GrpHom;
    HomSetoid := GrpHomSetoid;
    comp := GrpComp;
    id := GrpId;
}.
Proof.
  (* Proper *) Time proper; repeat red; intros; destruct x, y, x0, y0; cat;
    eapply (@comp_Proper MonCat); auto.
  (* Category laws *) all: grp.
Defined.

Require Import Cat.Instances.Setoids.

Definition Grp_zero_inv : SetoidHom Mon_init Mon_init.
Proof.
  red. exists (fun _ => tt). grp.
Defined.

Instance Grp_zero : Grp :=
{
    mon := Mon_init;
    inv := Grp_zero_inv
}.
Proof. all: grp. Defined.

Definition Grp_create (X : Grp) : Hom Grp_zero X.
Proof.
  do 3 red. exists (Mon_create X). grp.
Defined.

Instance Grp_has_init : has_init GrpCat :=
{
    init := Grp_zero;
    create := Grp_create
}.
Proof. grp. Defined.

Definition Grp_delete (X : Grp) : Hom X Grp_zero.
Proof.
  do 3 red. exists (Mon_delete X). grp.
Defined.

Instance Grp_has_term : has_term GrpCat :=
{
    term := Grp_zero;
    delete := Grp_delete
}.
Proof. grp. Defined.

Instance Grp_has_zero : has_zero GrpCat :=
{
    zero_is_initial := Grp_has_init;
    zero_is_terminal := Grp_has_term
}.
Proof. grp. Defined.

Definition Grp_prodOb_inv (X Y : Grp)
  : SetoidHom (Mon_prodOb X Y) (Mon_prodOb X Y).
Proof.
  red. exists (fun p : X * Y => (inv (fst p), inv (snd p))).
  (* TODO *) proper. destruct H. split; apply inv_Proper; assumption.
Defined.

Instance Grp_prodOb (X Y : Grp) : Grp :=
{
    mon := Mon_prodOb X Y;
    inv := Grp_prodOb_inv X Y
}.
Proof. all: destruct x; grp. Defined.

Definition Grp_proj1 (X Y : Grp) : Hom (Grp_prodOb X Y) X.
Proof.
  grp_simpl. exists (Mon_proj1 X Y). grp.
Defined.

Definition Grp_proj2 (X Y : Grp) : Hom (Grp_prodOb X Y) Y.
Proof.
  grp_simpl. exists (Mon_proj2 X Y). grp.
Defined.

Definition Grp_fpair (A B X : Grp) (f : Hom X A) (g : Hom X B)
    : Hom X (Grp_prodOb A B).
Proof.
  grp_simpl. exists (Mon_fpair f g). Time split; grp.
Defined.

Instance Grp_has_products : has_products GrpCat :=
{
    prodOb := Grp_prodOb;
    proj1 := Grp_proj1;
    proj2 := Grp_proj2;
    fpair := Grp_fpair
}.
Proof.
  grp.
  repeat split; cat.
Defined.

Definition AutOb (C : Cat) (X : Ob C) : Type := unit.

Definition AutHom {C : Cat} {X : Ob C} (_ _ : AutOb C X)
    : Type := {f : Hom X X | Iso f}.

Definition AutHom_Fun {C : Cat} {X : Ob C} (A B : AutOb C X)
    (f : AutHom A B) : Hom X X := proj1_sig f.

Coercion AutHom_Fun : AutHom >-> Hom.

Instance AutHomSetoid (C : Cat) (X : Ob C)
    : forall A B : AutOb C X, Setoid (AutHom A B) :=
{
    equiv := fun f g : AutHom A B =>
      @equiv _ (@HomSetoid C X X) f g
}.
Proof. grp. Defined.

Definition AutComp (C : Cat) (A : Ob C) (X Y Z : AutOb C A)
    (f : AutHom X Y) (g : AutHom Y Z) : AutHom X Z.
Proof.
  red. exists (f .> g). destruct f, g; simpl. apply iso_comp; auto.
Defined.

Definition AutId (C : Cat) (A : Ob C) (X : AutOb C A)
    : AutHom X X.
Proof.
  red. exists (id A). apply id_is_aut.
Defined.

Instance AutCat (C : Cat) (X : Ob C) : Cat :=
{
    Ob := AutOb C X;
    Hom := @AutHom C X;
    HomSetoid := @AutHomSetoid C X;
    comp := @AutComp C X;
    id := @AutId C X;
}.
Proof. all: grp. Defined.

(* TODO : finish Instance Cayley_Sgr (G : Grp) : Sgr :=
{
    carrier := {f : G -> G & {g : G | f = op g}};
    op := fun f g => fun x : G => g (f x)
}.
Proof.
  destruct 1 as [f1 [g1 H1]], 1 as [f2 [g2 H2]].
    exists (fun x => op g1 (op g2 x)). exists (op g1 g2).
    extensionality x. rewrite assoc. trivial.
  cat. grp'. repeat rewrite assoc.
Abort.*)

(*Instance Cayley_Mon (G : Grp) : Mon :=
{
    sgr := Cayley_Sgr G;
    neutr := fun x : G => x
}.
Proof. 
  all: intro; simpl; extensionality x; trivial.
Defined.

Instance Cayley_Grp (G : Grp) : Grp :=
{
    mon := Cayley_Mon G;
    (*inv := fun f : G -> G => *)
}.*)