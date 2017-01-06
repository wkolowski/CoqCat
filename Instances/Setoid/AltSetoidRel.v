Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.

Require Export Instances.Setoid.Setoids.

Definition SetoidRel (X Y : Setoid') : Type :=
    {R : X -> Y -> Prop |
      (forall (x x' : X) (y : Y), x == x' -> R x y <-> R x' y) /\
      (forall (x : X) (y y' : Y), y == y' -> R x y <-> R x y')}.

Definition SetoidRel_Fun (X Y : Setoid') (R : SetoidRel X Y)
    : X -> Y -> Prop := proj1_sig R.
Coercion SetoidRel_Fun : SetoidRel >-> Funclass.

Ltac setoidrelhom R := try intros until R;
match type of R with
  | SetoidRel _ _ =>
      let a := fresh R "_pres_l" in
      let b := fresh R "_pres_r" in destruct R as [R [a b]]
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
  setoidrel'; try rename x0 into y'; try rename y0 into x'.
    exists y'. split; auto. rewrite <- R_pres_l; eauto.
    exists y'. split; auto. rewrite (R_pres_l x x'); eauto.
    exists x0. split; try rewrite <- S_pres_r; eauto.
    exists x0. split; try rewrite S_pres_r; eauto.
Defined.

Definition SetoidRelId (X : Setoid') : SetoidRel X X.
Proof.
  red. exists equiv. repeat split; intros; try rewrite H; auto;
  try rewrite <- H; auto.
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
    rewrite f_pres_l; eauto.
    rewrite f_pres_r; eauto.
Defined.

Program Instance SetoidRel_has_init : has_init SetoidRelCat :=
{
    init := CoqSetoid_init;
    create := fun (X : Setoid') (e : Empty_set) _ => match e with end
}.
Next Obligation. split; destruct x. Defined.
Next Obligation. destruct x. Defined.

Program Instance SetoidRel_has_term : has_term SetoidRelCat :=
{
    term := CoqSetoid_init;
    delete := fun (X : Setoid') _ (e : Empty_set) => match e with end
}.
Next Obligation. split; destruct y. Defined.
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
  split; destruct x; try destruct x'; simpl in *; intros;
  try rewrite H; intuition eauto.
Defined.

Definition SetoidRel_proj2 (X Y : Setoid')
    : SetoidRel (SetoidRel_prodOb X Y) Y.
Proof.
  red. exists (fun (p : X + Y) (y : Y) =>
    match p with
      | inr y' => y == y'
      | _ => False
    end).
  split; destruct x; try destruct x'; simpl in *; intros;
  try rewrite H; intuition eauto.
Defined.

Definition SetoidRel_diag (A B X : Setoid')
    (R : SetoidRel X A) (S : SetoidRel X B)
    : SetoidRel X (SetoidRel_prodOb A B).
Proof.
  red. exists (fun (x : X) (p : A + B) =>
    match p with
      | inl a => R x a
      | inr b => S x b
    end).
  split; destruct y; try destruct y'; setoidrelhoms; simpl in *; eauto;
  inversion H.
Defined.

Instance SetoidRel_has_products : has_products SetoidRelCat :=
{
    prodOb := SetoidRel_prodOb;
    proj1 := SetoidRel_proj1;
    proj2 := SetoidRel_proj2;
    diag := SetoidRel_diag
}.
Proof.
  (* Proper *) repeat (red || split); simpl in *; intros; destruct y1.
    rewrite <- H. auto.
    rewrite <- H0. auto.
    rewrite H. auto.
    rewrite H0. auto.
  (* Product laws *) red. setoidrel'; repeat
  match goal with
    | p : _ + _ |- _ => destruct p
    | H : False |- _ => inversion H
  end.
    exists (inl y); eauto.
    rewrite f_pres_r; eauto.
    exists (inr y); eauto.
    rewrite g_pres_r; eauto.
    destruct (H x a), (H2 H1), H4, x0.
      rewrite y_pres_r; eauto.
      inversion H5.
    destruct (H0 x b), (H2 H1), H4, x0.
      inversion H5.
      rewrite y_pres_r; eauto.
    destruct (H x a). apply H3. exists (inl a). eauto.
    destruct (H0 x b). apply H3. exists (inr b). eauto.
Defined.

Definition SetoidRel_codiag (A B X : Setoid')
    (R : SetoidRel A X) (S : SetoidRel B X)
    : SetoidRel (SetoidRel_prodOb A B) X.
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