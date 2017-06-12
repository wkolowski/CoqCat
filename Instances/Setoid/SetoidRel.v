Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.

Require Export Cat.Instances.Setoids.

Definition SetoidRel (X Y : Setoid') : Type :=
    {R : X -> Y -> Prop | Proper (equiv ==> equiv ==> iff) R}.

Definition SetoidRel_Fun (X Y : Setoid') (R : SetoidRel X Y)
    : X -> Y -> Prop := proj1_sig R.
Coercion SetoidRel_Fun : SetoidRel >-> Funclass.

Ltac setoidrelhom R := try intros until R;
match type of R with
  | SetoidRel _ _ =>
      let a := fresh R "_Proper" in destruct R as [?R a]
  | Hom _ _ => progress simpl in R; setoidrelhom R
end.

Ltac setoidrelhoms := intros; repeat
match goal with
  | R : SetoidRel _ _ |- _ => setoidrelhom R
  | f : Hom _ _ |- _ => setoidrelhom f
end.

Ltac setoidrel' := repeat (my_simpl || setoidobs || setoidrelhoms || cat).
Ltac setoidrel := try (setoidrel'; fail).

Instance SetoidRel_Setoid (X Y : Setoid') : Setoid (SetoidRel X Y) :=
{
    equiv := fun (P Q : SetoidRel X Y) =>
      forall (x : X) (y : Y), P x y <-> Q x y
}.
Proof.
  solve_equiv; intros; try (edestruct H; eauto; fail).
    rewrite <- H0, <- H. auto.
    rewrite H, H0. auto.
Defined.

Definition SetoidRelComp (X Y Z : Setoid')
    (R : SetoidRel X Y) (S : SetoidRel Y Z) : SetoidRel X Z.
Proof.
  red. exists (fun (x : X) (z : Z) => exists y : Y, R x y /\ S y z).
  setoidrel'; repeat red; simpl; intros.
  repeat red in R_proper; repeat red in S_proper.
  split; destruct 1 as [y' [HR HS]];
  destruct (R_Proper x y H y' y' (Y_equiv_refl y'));
  destruct (S_Proper y' y' (Y_equiv_refl y') x0 y0 H0); eauto.
Defined.

Definition SetoidRelId (X : Setoid') : SetoidRel X X.
Proof.
  red. exists equiv. proper. reflexivity.
Defined.

Instance SetoidRelCat : Cat :=
{|
    Ob := Setoid';
    Hom := SetoidRel;
    HomSetoid := SetoidRel_Setoid;
    comp := SetoidRelComp;
    id := SetoidRelId
|}.
Proof.
  (* Proper *) repeat red; split; intros; destruct H1; simpl in *.
    eexists. erewrite <- H, <- H0. eauto.
    eexists. rewrite H, H0. eauto.
  (* Category laws *) all: setoidrel'.
    eapply f_Proper; eauto.
    eapply f_Proper. eauto. apply B_equiv_sym. eauto. eauto.
Defined.

Program Instance SetoidRel_has_init : has_init SetoidRelCat :=
{
    init := CoqSetoid_init;
    create := fun (X : Setoid') (e : Empty_set) _ => match e with end
}.
Next Obligation. proper. destruct x. Defined.
Next Obligation. destruct x. Defined.

Program Instance SetoidRel_has_term : has_term SetoidRelCat :=
{
    term := CoqSetoid_init;
    delete := fun (X : Setoid') _ (e : Empty_set) => match e with end
}.
Next Obligation. proper. destruct x0. Defined.
Next Obligation. destruct y. Defined.

Instance SetoidRel_has_zero : has_zero SetoidRelCat :=
{
    zero_is_initial := SetoidRel_has_init;
    zero_is_terminal := SetoidRel_has_term
}.
Proof. setoidrel. Defined.

Instance SetoidRel_prodOb (X Y : Setoid') : Setoid' :=
{
    carrier := X + Y;
    setoid :=
    {| equiv := fun p1 p2 : X + Y =>
      match p1, p2 with
        | inl x, inl x' => @equiv _ X x x'
        | inr y, inr y' => @equiv _ Y y y'
        | _, _ => False
      end
    |}
}.
Proof.
  repeat match goal with
    | p : _ + _ |- _ => destruct p
    | _ => solve_equiv
  end.
Defined.

Definition SetoidRel_proj1 (X Y : Setoid')
    : SetoidRel (SetoidRel_prodOb X Y) X.
Proof.
  red. exists (fun (p : X + Y) (x : X) =>
    match p with
      | inl x' => x == x'
      | _ => False
    end).
  repeat red.  destruct x, y; simpl; intros; intuition eauto.
    rewrite <- H0, <- H. auto.
    rewrite H, H0. auto.
Defined.

Definition SetoidRel_proj2 (X Y : Setoid')
    : SetoidRel (SetoidRel_prodOb X Y) Y.
Proof.
  red. exists (fun (p : X + Y) (y : Y) =>
    match p with
      | inr y' => y == y'
      | _ => False
    end).
  repeat red. destruct x, y; simpl; intros; intuition eauto.
    rewrite <- H0, <- H. auto.
    rewrite H0, H. auto.
Defined.

Definition SetoidRel_fpair (A B X : Setoid')
    (R : SetoidRel X A) (S : SetoidRel X B)
    : SetoidRel X (SetoidRel_prodOb A B).
Proof.
  red. exists (fun (x : X) (p : A + B) =>
    match p with
      | inl a => R x a
      | inr b => S x b
    end).
  repeat red; destruct x0, y0; setoidrelhoms; simpl in *; intuition eauto;
  try rewrite <- H0, <- H; auto;
  try rewrite H, H0; auto.
Defined.

Instance SetoidRel_has_products : has_products SetoidRelCat :=
{
    prodOb := SetoidRel_prodOb;
    proj1 := SetoidRel_proj1;
    proj2 := SetoidRel_proj2;
    fpair := SetoidRel_fpair
}.
Proof.
  (* Proper *) repeat red; destruct y1; setoidrelhoms; simpl in *;
  split; intros.
    rewrite <- H. auto.
    rewrite H. auto.
    rewrite <- H0. auto.
    rewrite H0. auto.
  (* Product laws *) red. setoidrel'; repeat
  match goal with
    | p : _ + _ |- _ => destruct p
    | H : False |- _ => inversion H
  end.
    exists (inl y). eauto.
    eapply f_Proper; eauto.
    exists (inr y); eauto.
    eapply g_Proper; eauto. repeat red in y_Proper.
    destruct (H x a) as [H' _]. destruct (H' H1) as [[y0_l | y0_r] [H'1 H'2]].
      eapply y_Proper; eauto. simpl. assumption.
      inversion H'2.
    destruct (H0 x b) as [H' _]. destruct (H' H1) as [[y0_l | y0_r] [H'1 H'2]].
      inversion H'2.
      eapply y_Proper; eauto. simpl. assumption.
    destruct (H x a) as [_ H']. apply H'. exists (inl a). eauto.
    destruct (H0 x b) as [_ H']. apply H'. exists (inr b). eauto.
Defined.

Definition SetoidRel_coprodOb := SetoidRel_prodOb.

Definition SetoidRel_coproj1 (X Y : Setoid')
    : SetoidRel X (SetoidRel_coprodOb X Y).
Proof.
  red. exists (fun (x : X) (p : X + Y) =>
    match p with
      | inl x' => x == x'
      | _ => False
    end).
  repeat red; destruct x0, y0; simpl; split; intros; eauto;
  try (inversion H0; fail).
    rewrite <- H, H1, H0. reflexivity.
    rewrite H, H0, H1. reflexivity.
Defined.

Definition SetoidRel_coproj2 (X Y : Setoid')
    : SetoidRel Y (SetoidRel_coprodOb X Y).
Proof.
  red. exists (fun (y : Y) (p : X + Y) =>
    match p with
      | inr y' => y == y'
      | _ => False
    end).
  repeat red; destruct x0, y0; simpl; split; intros; eauto;
  try (inversion H0; fail).
    rewrite <- H, H1, H0. reflexivity.
    rewrite H, H0, H1. reflexivity.
Defined.

Definition SetoidRel_copair (A B X : Setoid')
    (R : SetoidRel A X) (S : SetoidRel B X)
    : SetoidRel (SetoidRel_coprodOb A B) X.
Proof.
  red. exists (fun (p : A + B) (x : X) =>
    match p with
      | inl a => R a x
      | inr b => S b x
    end).
  repeat red; destruct x, y, R as [R R_proper], S as [S S_proper];
  simpl; intuition eauto;
  try rewrite <- H0, <- H; auto;
  try rewrite H, H0; auto.
Defined.

Instance SetoidRel_has_coproducts : has_coproducts SetoidRelCat :=
{
    coprodOb := SetoidRel_coprodOb;
    coproj1 := SetoidRel_coproj1;
    coproj2 := SetoidRel_coproj2;
    copair := SetoidRel_copair;
}.
Proof.
  (* copair is proper *) proper. destruct x1; eauto.
  (* Coproduct law *) red; setoidrel'; repeat
  match goal with
    | p : _ + _ |- _ => destruct p
    | H : False |- _ => inversion H
  end.
    exists (inl x); eauto.
    eapply f_Proper; eauto.
    exists (inr x); eauto.
    eapply g_Proper; eauto.
    destruct (H a y0), (H2 H1) as [[p1 | p2] [Hp1 Hp2]].
      eapply (y_Proper (inl a) (inl p1)); eauto.
      inversion Hp1.
    destruct (H0 b y0), (H2 H1) as [[p1 | p2] [Hp1 Hp2]].
      inversion Hp1.
      eapply (y_Proper (inr b) (inr p2)); eauto.
    destruct (H a y0). apply H3. exists (inl a); eauto.
    destruct (H0 b y0). apply H3. exists (inr b); eauto.
Defined.