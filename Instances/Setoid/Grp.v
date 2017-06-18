Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Logic.FunctionalExtensionality.

Require Export Cat.
Require Import Cat.Limits.InitTerm.
Require Import Cat.Limits.BinProdCoprod.

Require Export Cat.Instances.Setoid.Mon.

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

Ltac grp_simpl := simpl; intros;
try match goal with
  (* There's a group that wasn't destructed. *)
  (*| H : context [?op (?inv ?x) ?x] |- _ => rewrite inv_l in H
  | H : context [?op ?x (?inv ?x)] |- _ => rewrite inv_r in H*)
  | |- context [?op (?inv ?x) ?x] => rewrite inv_l
  | |- context [?op ?x (?inv ?x)] => rewrite inv_r
  (* There's some group that was destructed. *)
  | inv_l : forall g : _, ?op (?inv g) g == ?neutr |- _ =>
    try match goal with
      (*| H : context [?op (?inv ?x) ?x] |- _ => rewrite inv_l in H*)
      | |- context [?op (?inv ?x) ?x] => rewrite inv_l
    end
  | inv_r : forall g : _, ?op g (?inv g) = ?neutr |- _ =>
    try match goal with
      (*| H : context [?op ?x (?inv ?x)] |- _ => rewrite inv_r in H*)
      | |- context [?op ?x (?inv ?x)] => rewrite inv_r
    end
  (* Homomorphisms preserve inv. *)
  | (*f : ?X -> ?Y,*) pres_inv : forall g : _, ?f (?inv1 g) == ?inv2 (?f g)  |- _ =>
    match goal with
      | |- context [?f (?inv _)] => rewrite pres_inv
    end
end; mon_simpl.

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

Definition GrpHom (X Y : Grp) : Type := 
    {f : MonHom X Y | forall x : X, f (inv x) == inv (f x)}.

Definition GrpHom_MonHom (X Y : Grp) (f : GrpHom X Y)
    : MonHom X Y := proj1_sig f.
Coercion GrpHom_MonHom : GrpHom >-> MonHom.

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

Ltac grp' := repeat (grp_simpl || grpobs' || grphoms' || mon').
Ltac grp := try (grp'; fail).

Inductive exp : Grp -> Type :=
    | Id : forall X : Grp, exp X
    | Var : forall X : Grp, X -> exp X
    | Op : forall X : Grp, exp X -> exp X -> exp X
    | Mor : forall X Y : Grp, GrpHom X Y -> exp X -> exp Y
    | Inv : forall X : Grp, exp X -> exp X.

Arguments Id [X].
Arguments Var [X] _.
Arguments Op [X] _ _.
Arguments Mor [X Y] _ _ .
Arguments Inv [X] _.

(*Inductive exp (X : Grp) : Type :=
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
*)

Fixpoint expDenote {X : Grp} (e : exp X) : X :=
match e with
    | Id => neutr
    | Var v => v
    | Op e1 e2 => op (expDenote e1) (expDenote e2)
    | Mor f e' => f (expDenote e')
    | Inv x => inv (expDenote x)
end.

Require Import List.
Import ListNotations.

Fixpoint expDenoteL {X : Grp} (l : list X) : X :=
match l with
    | [] => neutr
    | h :: t => op h (expDenoteL t)
end.

Fixpoint fib (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n' as n'') => (*fib n'' +*) fib n'
end.

Eval compute in fib 10.

Fixpoint flatten {X : Grp} (e : exp X) {struct e} : list X :=
match e with
    | Id => []
    | Var v => [v]
    | Op e1 e2 => flatten e1 ++ flatten e2
    | Mor f Id => []
    (*| Mor f (Inv e') => *)
    | Mor f e' => map f (flatten e')
    (*| Inv (Inv e') => flatten e'*)
    | Inv e' => rev (map inv (flatten e'))
end.

Lemma flatten_Hom : forall (X : Grp) (f : GrpHom X X) (e : exp X),
  e <> Id -> flatten (Mor f e) = map f (flatten e).
Proof.
  destruct e; auto.
Qed.

Lemma flatten_Inv : forall (X : Grp) (e : exp X),
  (forall e' : exp X, e <> Inv e') ->
  flatten (Inv e) = rev (map inv (flatten e)).
Proof.
  induction e; intros; trivial.
  (*contradiction (H e). trivial.*)
Qed.

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
    grp.
    assert (f (op h (expDenoteL t)) == op (f h) (f (expDenoteL t))).
      grp'.
      rewrite H. apply op_Proper.
        reflexivity.
        assumption.
Qed.

Lemma inv_Proper : forall (X : Grp), Proper (equiv ==> equiv) inv.
Proof.
  unfold Proper, respectful; intros. grpob X.
  simpl in *. destruct X_inv. simpl in *. f_equiv. assumption.
Qed.

Lemma expDenoteL_inv :
  forall (X : Grp) (l : list X),
    expDenoteL (map inv l) == inv (expDenoteL (rev l)).
Proof.
  induction l as [| h t]; simpl.
    rewrite inv_neutr. reflexivity.
    assert (inv (op h (expDenoteL t)) == op (inv (expDenoteL t)) (inv h)).
      rewrite inv_op. reflexivity.
      pose inv_Proper. rewrite expDenoteL_app. rewrite inv_op. simpl.
        apply op_Proper.
          grp.
          assumption.
Qed.

Theorem flatten_correct :
  forall (X : Grp) (e : exp X),
    expDenoteL (flatten e) == expDenote e.
Proof.
  induction e.
    reflexivity.
    mon.
    simpl. rewrite expDenoteL_app. apply op_Proper; assumption.
    destruct e; simpl; try rewrite expDenoteL_hom; grp.
    destruct e; simpl in *.
      rewrite inv_neutr. reflexivity.
      grp.
      pose inv_Proper. rewrite <- IHe.
      rewrite map_app. rewrite rev_app_distr. do 2 rewrite <- map_rev.
        rewrite expDenoteL_app.
          replace (flatten e1 ++ flatten e2) with
            (rev (rev (flatten e1 ++ flatten e2))).
          rewrite <- expDenoteL_inv. rewrite rev_app_distr.
            rewrite map_app. rewrite expDenoteL_app. reflexivity.
          apply rev_involutive.
      rewrite <- map_rev. rewrite expDenoteL_inv. rewrite rev_involutive.
        apply inv_Proper. assumption.
      rewrite <- map_rev. rewrite expDenoteL_inv. apply inv_Proper.
        rewrite rev_involutive. assumption.
Qed.

Theorem grp_reflect :
  forall (X : Grp) (e1 e2 : exp X),
    expDenoteL (flatten e1) == expDenoteL (flatten e2) ->
      expDenote e1 == expDenote e2.
Proof.
  induction e1; intros; repeat rewrite flatten_correct in H;
  assumption.
Qed.

Ltac reify e :=
lazymatch e with
    | @neutr ?X => idtac X; constr:(@Id X)
    | op ?e1 ?e2 =>
        let e1' := reify e1 in
        let e2' := reify e2 in constr:(Op e1' e2')
    | SetoidHom_Fun (SgrHom_Fun (MonHom_SgrHom (GrpHom_MonHom ?f))) ?e =>
        let e' := reify e in constr:(Mor f e')
    (*| inv ?e =>
        let e' := reify e in constr:(Inv e')*)
    | ?v => constr:(Var v)
end.

Ltac grp2 := simpl; intros;
match goal with
    | |- ?e1 == ?e2 =>
        let e1' := reify e1 in
        let e2' := reify e2 in
          change (expDenote e1' == expDenote e2');
          apply grp_reflect; simpl
end.

Ltac grp2' := mon2; try reflexivity.

Goal forall (X : Grp) (a b c : X),
  op a (op b c) == op (op a b) c.
Proof.
  grp2'.
Qed.

Goal forall (X : Grp) (f : GrpHom X X) (a b : X),
  f (op a b) == op (f a) (f b).
Proof.
  grp2'.
Qed.

Goal forall (X : Grp) (f : GrpHom X X) (a b c : X),
  op (f (f neutr)) (op (f a) (f (op b c))) ==
  op (f a) (op (f b) (f c)).
Proof.
  grp2'.
Qed.

Goal forall (X Y Z : Grp) (f : GrpHom X Y) (g : GrpHom Y Z),
  g (f neutr) == neutr.
Proof.
  intros.
  let e := reify constr:(@neutr X) in pose e.
  (* TODO : problem with neutral element. It's argument is Mon,
     but reify requires it to be Grp. *)
Qed.

Instance GrpHomSetoid (X Y : Grp) : Setoid (GrpHom X Y) :=
{
  equiv := fun f g : GrpHom X Y =>
      @equiv _ (SgrHomSetoid X Y) (proj1_sig f) (proj1_sig g)
}.
Proof. apply Setoid_kernel_equiv. Defined.

Definition GrpComp (X Y Z : Grp) (f : GrpHom X Y) (g : GrpHom Y Z)
    : GrpHom X Z.
Proof.
  red. exists (MonComp f g). grp2.
Defined.

Definition GrpId (X : Grp) : GrpHom X X.
Proof. red. exists (MonId X). grp. Defined.

Instance GrpCat : Cat :=
{
    Ob := Grp;
    Hom := GrpHom;
    HomSetoid := GrpHomSetoid;
    comp := GrpComp;
    id := GrpId;
}.
Proof.
  (* Proper *) proper. Time repeat red; intros; destruct x, y, x0, y0; cat;
    eapply (@comp_Proper MonCat); auto.
  (* Category laws *) Time all: grp.
Defined.

Instance Grp_zero : Grp :=
{
    mon := Mon_init;
    inv := fun _ => tt
}.
Proof. all: grp. Defined.

Definition Grp_create (X : Grp) : Hom Grp_zero X.
Proof.
  repeat red. exists (Mon_create X). grp_simpl. auto.
Defined.

Instance Grp_has_init : has_init GrpCat :=
{
    init := Grp_zero;
    create := Grp_create
}.
Proof. grpobs; grphoms'. destruct x. auto. Defined.

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

Instance Grp_prod (X Y : Grp) : Grp :=
{
    mon := Mon_prod X Y;
    inv := fun p : X * Y => (inv (fst p), inv (snd p));
}.
Proof. all: destruct x; grp. Defined.

Definition Grp_proj1 (X Y : Grp) : Hom (Grp_prod X Y) X.
Proof.
  grp_simpl. exists (Mon_proj1 X Y). grp.
Defined.

Definition Grp_proj2 (X Y : Grp) : Hom (Grp_prod X Y) Y.
Proof.
  grp_simpl. exists (Mon_proj2 X Y). grp.
Defined.

Definition Grp_fpair (A B X : Grp) (f : Hom X A) (g : Hom X B)
    : Hom X (Grp_prod A B).
Proof.
  grp_simpl. exists (Mon_fpair _ _ _ f g).
  grphoms'. grp_simpl. auto.
Defined.

Instance Grp_has_products : has_products GrpCat :=
{
    prodOb := Grp_prod;
    proj1 := Grp_proj1;
    proj2 := Grp_proj2;
    fpair := Grp_fpair
}.
Proof.
  grp_simpl. grphoms'. rewrite H, H0. auto.
  grp_simpl. repeat split.
    intros. grphoms'. destruct H. rewrite H, H0. destruct (y x). auto.
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
Proof. repeat split; red; solve_equiv. Defined.

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
Proof. proper. all: cat. Defined.

(* TODO : finish *) Instance Cayley_Sgr (G : Grp) : Sgr :=
{
    carrier := {f : G -> G & {g : G | f = op g}};
    (*op := fun f g => fun x : G => g (f x)*)
}.
Proof.
  destruct 1 as [f1 [g1 H1]], 1 as [f2 [g2 H2]].
    exists (fun x => op g1 (op g2 x)). exists (op g1 g2).
    extensionality x. rewrite assoc. trivial.
  cat. grp'. repeat rewrite assoc.
Abort.

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