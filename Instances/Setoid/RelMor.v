Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.

Require Export Cat.Instances.Setoids.

Class SetoidRel (X Y : Setoid') : Type :=
{
    rel : X -> Y -> Prop;
    rel_Proper :> Proper (equiv ==> equiv ==> iff) rel
}.

Coercion rel : SetoidRel >-> Funclass.

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

Ltac rel' := repeat (intros;
match goal with
    | |- Proper _ _ => proper
    | |- Equivalence _ => solve_equiv
    | |- context [match ?x with _ => _ end] => destruct x; auto
    | _ : context [match ?x with _ => _ end] |- _ => destruct x; auto
    | |- _ <-> _ => split; intros; my_simpl
    | H : _ == _ |- _ => progress (rewrite H in *)
    | H : forall _ _, _ <-> _ |- _ => edestruct H; clear H
    | |- exists _, _ => eexists
end); cat.

Ltac setoidrel' := repeat (my_simpl || setoidobs || setoidrelhoms || cat).
Ltac setoidrel := try (setoidrel'; fail).

Ltac rel := repeat rel'; setoidrel'; rel'.

#[refine]
Instance SetoidRel_Setoid (X Y : Setoid') : Setoid (SetoidRel X Y) :=
{
    equiv := fun (P Q : SetoidRel X Y) =>
      forall (x : X) (y : Y), P x y <-> Q x y
}.
Proof.
  solve_equiv; intro; edestruct H; try edestruct H0; eauto.
Defined.

#[refine]
Instance SetoidRelComp (X Y Z : Setoid')
    (R : SetoidRel X Y) (S : SetoidRel Y Z) : SetoidRel X Z :=
{
    rel := fun (x : X) (z : Z) => exists y : Y, R x y /\ S y z
}.
Proof. rel. Defined.

Instance SetoidRelId (X : Setoid') : SetoidRel X X :=
{
    rel := equiv
}.

#[refine]
Instance SetoidRelCat : Cat :=
{|
    Ob := Setoid';
    Hom := SetoidRel;
    HomSetoid := SetoidRel_Setoid;
    comp := SetoidRelComp;
    id := SetoidRelId
|}.
Proof. all: rel. Defined.

Program Instance SetoidRel_has_init : has_init SetoidRelCat :=
{
    init := CoqSetoid_init;
    create := fun X : Setoid' =>
        {| rel := fun (e : Empty_set) _ => match e with end |}
}.
Next Obligation. rel. Defined.
Next Obligation. rel. Defined.

Program Instance SetoidRel_has_term : has_term SetoidRelCat :=
{
    term := CoqSetoid_init;
    delete := fun X : Setoid' =>
        {| rel := fun _ (e : Empty_set) => match e with end |}
}.
Next Obligation. rel. Defined.
Next Obligation. rel. Defined.

#[refine]
Instance SetoidRel_has_zero : has_zero SetoidRelCat :=
{
    zero_is_initial := SetoidRel_has_init;
    zero_is_terminal := SetoidRel_has_term
}.
Proof. rel. Defined.

#[refine]
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
Proof. rel. Defined.

#[refine]
Instance SetoidRel_proj1 (X Y : Setoid')
    : SetoidRel (SetoidRel_prodOb X Y) X :=
{
    rel := fun (p : X + Y) (x : X) =>
    match p with
      | inl x' => x == x'
      | _ => False
    end
}.
Proof. rel. Defined.

#[refine]
Instance SetoidRel_proj2 (X Y : Setoid')
    : SetoidRel (SetoidRel_prodOb X Y) Y :=
{
    rel := fun (p : X + Y) (y : Y) =>
    match p with
      | inr y' => y == y'
      | _ => False
    end
}.
Proof. rel. Defined.

#[refine]
Instance SetoidRel_fpair (A B X : Setoid')
    (R : SetoidRel X A) (S : SetoidRel X B)
    : SetoidRel X (SetoidRel_prodOb A B) :=
{
    rel := fun (x : X) (p : A + B) =>
    match p with
      | inl a => R x a
      | inr b => S x b
    end
}.
Proof. rel. Defined.

#[refine]
Instance SetoidRel_has_products : has_products SetoidRelCat :=
{
    prodOb := SetoidRel_prodOb;
    proj1 := SetoidRel_proj1;
    proj2 := SetoidRel_proj2;
    fpair := SetoidRel_fpair
}.
Proof.
  (* Proper *) rel.
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

#[refine]
Instance SetoidRel_coproj1 (X Y : Setoid')
    : SetoidRel X (SetoidRel_coprodOb X Y) :=
{
    rel := fun (x : X) (p : X + Y) =>
    match p with
      | inl x' => x == x'
      | _ => False
    end
}.
Proof. rel. Defined.

#[refine]
Instance SetoidRel_coproj2 (X Y : Setoid')
    : SetoidRel Y (SetoidRel_coprodOb X Y) :=
{
    rel := fun (y : Y) (p : X + Y) =>
    match p with
      | inr y' => y == y'
      | _ => False
    end
}.
Proof. rel. Defined.

#[refine]
Instance SetoidRel_copair (A B X : Setoid')
    (R : SetoidRel A X) (S : SetoidRel B X)
    : SetoidRel (SetoidRel_coprodOb A B) X :=
{
    rel := fun (p : A + B) (x : X) =>
    match p with
      | inl a => R a x
      | inr b => S b x
    end
}.
Proof. rel. Defined.

#[refine]
Instance SetoidRel_has_coproducts : has_coproducts SetoidRelCat :=
{
    coprodOb := SetoidRel_coprodOb;
    coproj1 := SetoidRel_coproj1;
    coproj2 := SetoidRel_coproj2;
    copair := SetoidRel_copair;
}.
Proof.
  (* copair is proper *) rel.
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