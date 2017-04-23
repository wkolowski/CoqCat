Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat".

Require Import Logic.FunctionalExtensionality.

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export Instances.Set.Mon.

Class Grp : Type :=
{
    mon :> Mon;
    inv : mon -> mon;
    inv_l : forall x : mon, op (inv x) x = neutr;
    inv_r : forall x : mon, op x (inv x) = neutr
}.

Hint Resolve inv_l inv_r.

Coercion mon : Grp >-> Mon.

Ltac grp_simpl := simpl; intros;
try match goal with
  (* There's a group that wasn't destructed. *)
  (*| H : context [?op (?inv ?x) ?x] |- _ => rewrite inv_l in H
  | H : context [?op ?x (?inv ?x)] |- _ => rewrite inv_r in H*)
  | |- context [?op (?inv ?x) ?x] => rewrite inv_l
  | |- context [?op ?x (?inv ?x)] => rewrite inv_r
  (* There's some group that was destructed. *)
  | inv_l : forall g : _, ?op (?inv g) g = ?neutr |- _ =>
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
  | (*f : ?X -> ?Y,*) pres_inv : forall g : _, ?f (?inv1 g) = ?inv2 (?f g)  |- _ =>
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
    {f : MonHom X Y | forall x : X, f (inv x) = inv (f x)}.

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

Instance GrpHomSetoid (X Y : Grp) : Setoid (GrpHom X Y) :=
{
  equiv := fun f g : GrpHom X Y =>
      @equiv _ (SgrHomSetoid X Y) (proj1_sig f) (proj1_sig g)
}.
Proof. apply Setoid_kernel_equiv. Defined.

Definition GrpComp (X Y Z : Grp) (f : GrpHom X Y) (g : GrpHom Y Z)
    : GrpHom X Z.
Proof.
  red. destruct f as [f Hf0], g as [g Hg0]. exists (MonComp _ _ _ f g).
  destruct f as [[f Hf1] Hf2], g as [[g Hg1] Hg2]; simpl in *.
  intro. rewrite Hf0, Hg0. auto.
Defined.

Definition GrpId (X : Grp) : GrpHom X X.
Proof. red. exists (MonId X). simpl. auto. Defined.

Instance GrpCat : Cat :=
{
    Ob := Grp;
    Hom := GrpHom;
    HomSetoid := GrpHomSetoid;
    comp := GrpComp;
    id := GrpId;
}.
Proof.
  (* Proper *) repeat red; intros. destruct x, y, x0, y0; cat.
    eapply (@comp_Proper MonCat); auto.
  (* Category laws *) all: intros; grphoms'; grp.
Defined.

Theorem inv_involutive : forall (G : Grp) (g : G),
    inv (inv g) = g.
Proof.
  intros. assert (H : op (op (inv (inv g)) (inv g)) g = g).
    grp_simpl. auto.
  rewrite <- assoc in H. rewrite inv_l in H. rewrite neutr_r in H. auto.
Qed.

Theorem neutr_unique_l : forall (G : Grp) (e : G),
    (forall g : G, op e g = g) -> e = neutr.
Proof.
  intros. assert (op e neutr = e). grp.
  assert (op e neutr = neutr). apply H.
  rewrite H0 in H1. auto.
Defined.

Theorem neutr_unique_r : forall (G : Grp) (e : G),
    (forall g : G, op g e = g) -> e = neutr.
Proof.
  intros.
  assert (op neutr e = e). grp.
  assert (op neutr e = neutr). apply H.
  rewrite H0 in H1. auto.
Defined.

Theorem inv_op : forall (G : Grp) (a b : G),
    inv (op a b) = op (inv b) (inv a).
Proof.
  intros.
  assert (forall x y : G, op (op x y) (inv (op x y)) = neutr). auto.
  assert (forall x y : G, op (op x y) (op (inv y) (inv x)) = neutr).
    intros. rewrite <- assoc. rewrite (assoc y _). rewrite inv_r.
    rewrite neutr_l. auto.
  replace (inv (op a b)) with (op (inv (op a b)) neutr); auto.
    rewrite <- (H0 a b). rewrite assoc. rewrite inv_l. auto.
Defined.

Theorem inv_neutr : forall (G : Grp), inv neutr = neutr.
Proof.
  intros. apply neutr_unique_l. intro.
  rewrite <- inv_involutive at 1. rewrite inv_op.
  rewrite inv_involutive. rewrite neutr_r. apply inv_involutive.
Defined.

Hint Resolve inv_involutive neutr_unique_l neutr_unique_r inv_op inv_neutr.

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

Definition Grp_diag (A B X : Grp) (f : Hom X A) (g : Hom X B)
    : Hom X (Grp_prod A B).
Proof.
  grp_simpl. exists (Mon_diag _ _ _ f g).
  grphoms'. grp_simpl. auto.
Defined.

Instance Grp_has_products : has_products GrpCat :=
{
    prodOb := Grp_prod;
    proj1 := Grp_proj1;
    proj2 := Grp_proj2;
    diag := Grp_diag
}.
Proof.
  grp_simpl. grphoms'. rewrite H, H0. auto.
  grp_simpl. repeat split.
    intros. grphoms'. destruct H. rewrite H, H0. destruct (y x). auto.
Defined.

Instance Cayley_Sgr (G : Grp) : Sgr :=
{
    carrier := {f : G -> G & {g : G | f = op g}};
    (*op := fun f g => fun x : G => g (f x)*)
}.
Proof.
  destruct 1 as [f1 [g1 H1]], 1 as [f2 [g2 H2]].
    exists (fun x => op g1 (op g2 x)). exists (op g1 g2).
    extensionality x. rewrite assoc. trivial.
  cat. grp'. repeat rewrite assoc. (* TODO: finish *) 
Defined.

Instance Cayley_Mon (G : Grp) : Mon :=
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
    inv := fun f : G -> G => 
}.