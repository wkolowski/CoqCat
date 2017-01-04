Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.

Require Export Instances.Setoid.Setoids.

Definition SetoidRel (X Y : Setoid') : Type :=
    {R : X -> Y -> Prop | Proper (equiv ==> equiv ==> iff) R}.

Definition SetoidRel_Fun (X Y : Setoid') (R : SetoidRel X Y)
    : X -> Y -> Prop := proj1_sig R.
Coercion SetoidRel_Fun : SetoidRel >-> Funclass.

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
  repeat red; intros.
  setoidobs; destruct R as [R R_proper], S as [S S_proper]; simpl in *.
  split; destruct 1 as [y' [HR HS]];
  repeat red in R_proper; repeat red in S_proper;
  destruct (R_proper x y H y' y' (Y_equiv_refl y'));
  destruct (S_proper y' y' (Y_equiv_refl y') x0 y0 H0); eauto.
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
  (* Category laws *) all: intros; repeat
    match goal with
      | R : SetoidRel _ _ |- _ => destruct R
    end; setoidobs; simpl in *; setoid'.
      eapply p; eauto.
      eapply p. eauto. apply B_equiv_sym. eauto. eauto.
Defined.

(* TODO: prove all this shit *)
Instance Rel_has_init : has_init Rel :=
{
    init := Empty_set;
    create := fun (X : Set) (e : Empty_set) (x : X) => match e with end
}.
Proof. cat. Defined.

Instance Rel_has_term : has_term Rel :=
{
    term := Empty_set;
    delete := fun (X : Set) (x : X) (e : Empty_set) => match e with end
}.
Proof. cat. Defined.

Instance Rel_has_zero : has_zero Rel :=
{
    zero_is_initial := Rel_has_init;
    zero_is_terminal := Rel_has_term
}.
Proof. cat. Defined.

Ltac solve :=
match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | _ => try subst; eauto
end.

Theorem Rel_product : forall A B : Ob Rel,
    product Rel (A + B) (fun (p : A + B) (a : A) => p = inl a)
      (fun (p : A + B) (b : B) => p = inr b).
Proof.
  unfold product; simpl. intros A B X R S.
  exists (fun (x : X) (ab : A + B) => match ab with
      | inl a => R x a
      | inr b => S x b
  end).
  repeat (red || split); intros.
    exists (inl b). auto.
    destruct H, x, H; inversion H0; subst; auto.
    exists (inr b). auto.
    destruct H, x, H; inversion H0; subst; auto.
    destruct H, b. 
      destruct (H a a0), (H2 H0), H4; subst. auto.
      destruct (H1 a b), (H2 H0), H4; subst. auto.
    destruct H, b.
      destruct (H a a0). apply H3. eauto.
      destruct (H1 a b). apply H3. eauto.
Restart.
  unfold product; simpl. intros A B X R S.
  exists (fun (x : X) (ab : A + B) => match ab with
      | inl a => R x a
      | inr b => S x b
  end).
  repeat (red || split); intros.
    all: try eexists; cat.
    destruct b; [edestruct H, H2 | edestruct H1, H2]; cat.
    destruct b; [edestruct H, H2 | edestruct H1, H2]; cat.
Defined.

Theorem Rel_coproduct : forall A B : Ob Rel,
    coproduct Rel (A + B) (fun (a : A) (p : A + B) => p = inl a)
      (fun (b : B) (p : A + B) => p = inr b).
Proof.
  unfold coproduct; simpl. intros A B X R S.
  exists (fun (ab : A + B) (x : X) => match ab with
      | inl a => R a x
      | inr b => S b x
  end).
  repeat (red || split); intros.
    all: try eexists; cat.
    destruct a; [edestruct H, H2 | edestruct H1, H2]; cat.
    destruct a; [edestruct H, H2 | edestruct H1, H2]; cat.
Defined.

Hint Resolve Rel_product Rel_coproduct.

Theorem Rel_biproduct : forall A B : Ob Rel,
    biproduct Rel (A + B)
      (fun (p : A + B) (a : A) => p = inl a)
      (fun (p : A + B) (b : B) => p = inr b)      
      (fun (a : A) (p : A + B) => p = inl a)
      (fun (b : B) (p : A + B) => p = inr b).
Proof. red; cat. Defined.

Instance Rel_has_all_products : has_all_products Rel :=
{
    bigProdOb := fun (J : Set) (A : J -> Ob Rel) => {j : J & A j};
    bigProj := fun (J : Set) (A : J -> Ob Rel) (j : J) =>
        fun (p : {j : J & A j}) (x : A j) => projT1 p = j /\ JMeq (projT2 p) x;
    bigDiag := fun (J : Set) (A : J -> Ob Rel) (X : Ob Rel)
      (f : forall j : J, Hom X (A j)) (x : X) (p : {j : J & A j}) =>
        f (projT1 p) x (projT2 p)
}.
Proof.
  (* bigDiag is proper *) cat.
  (* Product law *) red; cat; simpl in *.
    exists (existT A j b); simpl. auto.
    destruct (H x a a0), (H1 H0), x0; simpl in *. cat.
    destruct (H x a a0); simpl in *. cat.
Defined.

Instance Rel_has_all_coproducts : has_all_coproducts Rel :=
{
    bigCoprodOb := fun (J : Set) (A : J -> Ob Rel) => {j : J & A j};
    bigCoproj := fun (J : Set) (A : J -> Ob Rel) (j : J) =>
        fun (x : A j) (p : {j : J & A j}) => projT1 p = j /\ JMeq (projT2 p) x;
    bigCodiag := fun (J : Set) (A : J -> Ob Rel) (X : Ob Rel)
      (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) (x : X) =>
        f (projT1 p) (projT2 p) x
}.
Proof.
  (* bigCodiag is proper *) cat.
  (* Coproduct law *) red; cat; simpl in *.
    exists (existT A j a); simpl. auto.
    destruct (H x a b), (H1 H0), x0. cat.
    destruct (H x a b). apply H2. eexists. cat.
Defined.

Instance Rel_has_all_biproducts : has_all_biproducts Rel :=
{
    bigProduct := Rel_has_all_products;
    bigCoproduct := Rel_has_all_coproducts
}.
Proof. cat. Defined.
