Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.
Require Export Equalizer.
Require Export BigProdCoprod.
Require Import Exponential.
Require Import CartesianClosed.

Require Import Cat.Functor.

Set Implicit Arguments.

Class Setoid' : Type :=
{
    carrier : Type;
    setoid :> Setoid carrier
}.

Coercion carrier : Setoid' >-> Sortclass.
Coercion setoid : Setoid' >-> Setoid.

Ltac setoidob S := try intros until S;
match type of S with
  | Setoid =>
    let a := fresh S "_equiv" in
    let b := fresh S "_equiv_refl" in
    let c := fresh S "_equiv_sym" in
    let d := fresh S "_equiv_trans" in destruct S as [a [b c d]];
      red in a; red in b; red in c; red in d
  | Setoid' =>
    let a := fresh S "_equiv" in
    let b := fresh S "_equiv_refl" in
    let c := fresh S "_equiv_sym" in
    let d := fresh S "_equiv_trans" in destruct S as [S [a [b c d]]];
      red in a; red in b; red in c; red in d
  | Ob _ => progress simpl in S; setoidob S
end.

Ltac setoidobs := intros; repeat
match goal with
  | S : Setoid |- _ => setoidob S
  | S : Setoid' |- _ => setoidob S
  | S : Ob _ |- _ => setoidob S
end.

Class SetoidHom (X Y : Setoid') : Type :=
{
    func : X -> Y;
    func_Proper :> Proper (@equiv _ X ==> @equiv _ Y) func
}.

Arguments func [X Y] _.
Arguments func_Proper [X Y] _.

Coercion func : SetoidHom >-> Funclass.

Ltac setoidhom f := try intros until f;
match type of f with
  | SetoidHom _ _ =>
    let a := fresh f "_pres_equiv" in destruct f as [f a];
      repeat red in a
  | Hom _ _ => progress simpl in f; setoidhom f
end.

Ltac setoidhoms := intros; repeat
match goal with
  | f : SetoidHom _ _ |- _ => setoidhom f
  | f : Hom _ _ |- _ => setoidhom f
end.

Ltac setoid_simpl := repeat (red || split || simpl in * || intros).
Ltac setoid_simpl' := repeat (setoid_simpl || setoidhoms || setoidobs).

Ltac setoid' := repeat
match goal with
    | |- Proper _ _ => proper
    | |- Equivalence _ _ => solve_equiv
    | _ => setoid_simpl || cat || setoidhoms || setoidobs
end.

Ltac setoid := try (setoid'; fail).

#[refine]
Instance SetoidComp (X Y Z : Setoid') (f : SetoidHom X Y)
    (g : SetoidHom Y Z) : SetoidHom X Z :=
{
    func := fun x : X => g (f x)
}.
Proof. setoid. Defined.

#[refine]
Instance SetoidId (X : Setoid') : SetoidHom X X :=
{
    func := fun x : X => x
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid : Cat :=
{|
    Ob := Setoid';
    Hom := SetoidHom;
    HomSetoid := fun X Y : Setoid' =>
    {|
        equiv := fun f g : SetoidHom X Y =>
          forall x : X, @equiv _ (@setoid Y) (f x) (g x)
    |};
    comp := SetoidComp;
    id := SetoidId
|}.
Proof. all: setoid. Defined.

#[refine]
Instance const (X Y : Setoid') (y : Y) : SetoidHom X Y :=
{
    func := fun _ => y
}.
Proof. setoid. Defined.

Arguments const _ [Y] _.

Theorem CoqSetoid_mon_char : forall (X Y : Setoid') (f : SetoidHom X Y),
    Mon f <-> injectiveS f.
Proof.
  unfold Mon, injectiveS; split; intros.
    specialize (H _ (const Y a) (const Y a')). cbn in H.
      apply H; auto. exact (f a).
    cbn. intro. apply H. apply H0.
Defined.

Theorem CoqSetoid_sur_is_epi : forall (X Y : Setoid') (f : SetoidHom X Y),
    surjectiveS f -> Epi f.
Proof.
  unfold Epi, surjectiveS; intros. cbn in *. intro.
  destruct (H x) as [a eq].
  rewrite (func_Proper g x), (func_Proper h x).
    apply H0.
    all: rewrite eq; reflexivity.
Defined.

Theorem CoqSetoid_sec_is_inj : forall (X Y : Setoid') (f : SetoidHom X Y),
    Sec f -> injectiveS f.
Proof.
  unfold Sec, injectiveS; intros.
  destruct H as [g H]. cbn in *. cut (g (f a) == g (f a')).
    intro. rewrite !H in H1. assumption.
    setoid.
Defined.

Definition surjectiveS_skolem
  {A B : Type} {SA : Setoid A} {SB : Setoid B} (f : A -> B) : Prop :=
    exists g : B -> A, Proper (equiv ==> equiv) g /\
      forall b : B, f (g b) == b.

Theorem CoqSetoid_ret_char : forall (X Y : Setoid') (f : SetoidHom X Y),
    Ret f <-> surjectiveS_skolem f.
Proof.
  unfold Ret, surjectiveS; split; simpl; intros.
    destruct H as [g H]. red. exists g. setoid'.
    do 2 destruct H. exists {| func := x; func_Proper := H |}. cat.
Qed.

#[refine]
Instance CoqSetoid_init : Setoid' :=
{
    carrier := Empty_set;
    setoid := {| equiv := fun (x y : Empty_set) => match x with end |}
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_create (X : Setoid') : SetoidHom CoqSetoid_init X :=
{
    func := fun e : Empty_set => match e with end
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_has_init : has_init CoqSetoid :=
{
    init := CoqSetoid_init;
    create := CoqSetoid_create;
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_term : Setoid' :=
{
    carrier := unit;
    setoid := {| equiv := fun _ _ => True |};
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_delete (X : Setoid') : SetoidHom X CoqSetoid_term :=
{
    func := fun _ => tt
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_has_term : has_term CoqSetoid :=
{
    term := CoqSetoid_term;
    delete := CoqSetoid_delete;
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_prodOb (X Y : Setoid') : Setoid' :=
{
    carrier := X * Y;
    setoid := {| equiv := fun p1 p2 : X * Y =>
      @equiv _ (@setoid X) (fst p1) (fst p2) /\
      @equiv _ (@setoid Y) (snd p1) (snd p2) |}
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_proj1 (X Y : Setoid')
    : SetoidHom (CoqSetoid_prodOb X Y) X :=
{
    func := fst
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_proj2 (X Y : Setoid')
    : SetoidHom (CoqSetoid_prodOb X Y) Y :=
{
    func := snd
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_fpair (A B X : Setoid')
    (f : SetoidHom X A) (g : SetoidHom X B)
    : SetoidHom X (CoqSetoid_prodOb A B) :=
{
    func := fun x : X => (f x, g x)
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_has_products : has_products CoqSetoid :=
{
    prodOb := CoqSetoid_prodOb;
    proj1 := CoqSetoid_proj1;
    proj2 := CoqSetoid_proj2;
    fpair := CoqSetoid_fpair
}.
Proof. all: setoid'. Time Defined.

#[refine]
Instance CoqSetoid_coprodOb (X Y : Setoid') : Setoid' :=
{
    carrier := sum X Y;
    setoid := {| equiv := fun p1 p2 : sum X Y =>
      match p1, p2 with
        | inl x, inl x' => @equiv _ (@setoid X) x x'
        | inr y, inr y' => @equiv _ (@setoid Y) y y'
        | _, _ => False
      end |}
}.
Proof.
  setoid'; destruct x; try destruct y; try destruct z; setoid.
Defined.

Instance CoqSetoid_coproj1 (X Y : Setoid')
    : SetoidHom X (CoqSetoid_coprodOb X Y).
Proof.
  split with inl. proper. (* TODO : finish *)
Defined.

Instance CoqSetoid_coproj2 (X Y : Setoid')
    : SetoidHom Y (CoqSetoid_coprodOb X Y).
Proof.
  split with inr. proper.
Defined.

Instance CoqSetoid_copair (A B X : Setoid')
    (f : SetoidHom A X) (g : SetoidHom B X)
    : SetoidHom (CoqSetoid_coprodOb A B) X.
Proof.
  split with (fun p : sum A B =>
  match p with
    | inl a => f a
    | inr b => g b
  end).
  proper. destruct x, y; setoid.
Defined.

#[refine]
Instance CoqSetoid_has_coproducts : has_coproducts CoqSetoid :=
{
    coprodOb := CoqSetoid_coprodOb;
    coproj1 := CoqSetoid_coproj1;
    coproj2 := CoqSetoid_coproj2;
    copair := CoqSetoid_copair
}.
Proof.
  all: repeat match goal with
    | p : _ + _ |- _ => destruct p
    | _ => setoid'
  end.
Time Defined.

#[refine]
Instance CoqSetoid_eq_ob {X Y : Setoid'} (f g : SetoidHom X Y)
    : Setoid' :=
{
    carrier := {x : X | f x == g x};
    setoid := {| equiv := fun p1 p2 =>
      @equiv _ (@setoid X) (proj1_sig p1) (proj1_sig p2) |}
}.
Proof. setoid. Defined.

#[refine]
Instance CoqSetoid_eq_mor {X Y : Setoid'} (f g : SetoidHom X Y)
    : SetoidHom (CoqSetoid_eq_ob f g) X :=
{
    func := @proj1_sig _ _
}.
Proof. setoid. Defined.

Program Instance factorize {X Y E' : Setoid'} (f g : SetoidHom X Y)
    (e' : SetoidHom E' X) (H : forall x : E', f (e' x) == g (e' x))
    : SetoidHom E' (CoqSetoid_eq_ob f g) :=
{
    func := fun x => e' x
}.
Next Obligation. proper. Defined.

#[refine]
Instance CoqSetoid_has_equalizers : has_equalizers CoqSetoid :=
{
    eq_ob := @CoqSetoid_eq_ob;
    eq_mor := @CoqSetoid_eq_mor;
}.
Proof.
  repeat (red || split).
    destruct x. auto.
    intros. exists (factorize f g e' H). setoid'.
Defined.

Inductive CoqSetoid_coeq_equiv {X Y : Setoid'} (f g : SetoidHom X Y)
    : Y -> Y -> Prop :=
    | coeq_step : forall y y' : Y,
        y == y' -> CoqSetoid_coeq_equiv f g y y'
    | coeq_quot : forall x : X,
        CoqSetoid_coeq_equiv f g (f x) (g x)
    | coeq_sym : forall y y' : Y,
        CoqSetoid_coeq_equiv f g y y' ->
        CoqSetoid_coeq_equiv f g y' y
    | coeq_trans : forall y1 y2 y3 : Y,
        CoqSetoid_coeq_equiv f g y1 y2 ->
        CoqSetoid_coeq_equiv f g y2 y3 ->
        CoqSetoid_coeq_equiv f g y1 y3.

#[refine]
Instance CoqSetoid_coeq_ob {X Y : Setoid'} (f g : SetoidHom X Y) :
    Setoid' :=
{
    carrier := Y;
    setoid :=
      {| equiv := CoqSetoid_coeq_equiv f g |}
}.
Proof.
  solve_equiv.
    apply coeq_step. reflexivity.
    apply coeq_sym. assumption.
    eapply coeq_trans; eauto.
Defined.

#[refine]
Instance CoqSetoid_coeq_mor (X Y : Setoid') (f g : SetoidHom X Y)
    : SetoidHom Y (CoqSetoid_coeq_ob f g) :=
{
    func := fun y : Y => y
}.
Proof. do 2 red. intros. constructor. assumption. Defined.

#[refine]
Instance cofactorize (X Y Q' : Setoid') (f g : SetoidHom X Y)
    (q' : SetoidHom Y Q') (H : forall x : X, q' (f x) == q' (g x))
    : SetoidHom (CoqSetoid_coeq_ob f g) Q' :=
{
    func := q'
}.
Proof. proper. induction H0; subst; setoid'. Defined.

#[refine]
Instance CoqSetoid_has_coequalizers : has_coequalizers CoqSetoid :=
{
    coeq_ob := @CoqSetoid_coeq_ob;
    coeq_mor := CoqSetoid_coeq_mor
}.
Proof.
  setoid_simpl.
    apply coeq_quot.
    exists (cofactorize _ _ _ H). setoid'.
Defined.

#[refine]
Instance CoqSetoid_bigProdOb {J : Set} (A : J -> Setoid') : Setoid' :=
{
    carrier := forall j : J, A j;
    setoid := {| equiv := fun f g : forall j : J, A j =>
      forall j : J, @equiv _ (A j) (f j) (g j) |}
}.
Proof.
  split; red; intros; try rewrite H; try rewrite H0; reflexivity.
Defined.

Instance CoqSetoid_bigProj {J : Set} (A : J -> Setoid') (j : J)
    : SetoidHom (CoqSetoid_bigProdOb A) (A j).
Proof.
  split with (fun (f : forall j : J, A j) => f j). proper.
Defined.

Instance CoqSetoid_tuple {J : Set} {A : J -> Setoid'} {X : Setoid'}
    (f : forall j : J, SetoidHom X (A j))
    : SetoidHom X (CoqSetoid_bigProdOb A).
Proof.
  split with (fun x : X => (fun j : J => f j x)). proper.
Defined.

#[refine]
Instance CoqSetoid_has_all_products : has_all_products CoqSetoid :=
{
    bigProdOb := @CoqSetoid_bigProdOb;
    bigProj := @CoqSetoid_bigProj;
    tuple := @CoqSetoid_tuple
}.
Proof.
  simpl; intros; eauto.
  unfold big_product_skolem; red; simpl; split; intros;
  try reflexivity; eauto.
Defined.

Inductive equiv_hetero {A : Type} (S : Setoid A)
    : forall (B : Type), A -> B -> Prop :=
    | equiv_hetero_step : forall x y : A, x == y -> equiv_hetero S x y.

Hint Constructors equiv_hetero.

Theorem equiv_hetero_trans :
  forall (A B C : Type) (SA : Setoid A) (SB : Setoid B)
  (x : A) (y : B) (z : C), A = B -> JMeq SA SB ->
    equiv_hetero SA x y -> equiv_hetero SB y z -> equiv_hetero SA x z.
Proof.
  intros. Require Import Program. subst.
  apply JMeq_eq in H0. subst. dependent destruction H1.
  dependent destruction H2. constructor. rewrite H. assumption.
Qed.

Arguments equiv_hetero_trans [A B C SA SB x y z] _ _ _ _.

#[refine]
Instance CoqSetoid_bigCoprodOb {J : Set} (A : J -> Setoid') : Setoid' :=
{
    carrier := {j : J & A j};
    setoid :=
    {|
        equiv := fun x y : {j : J & A j} =>
          projT1 x = projT1 y /\
            equiv_hetero (A (projT1 x)) (projT2 x) (projT2 y)
    |}
}.
Proof.
  split; red; destruct x; try destruct y; try destruct z;
  simpl; intros.
    split; auto. constructor. reflexivity.
    destruct H; subst. split; auto. inversion H0; subst.
      constructor. Require Import Program. apply inj_pair2 in H.
      rewrite H1, <- H. reflexivity.
    destruct H, H0; split.
      rewrite H, H0. auto.
      subst. eapply (equiv_hetero_trans (eq_refl) (JMeq_refl) H1 H2).
Defined.

#[refine]
Instance CoqSetoid_bigCoproj {J : Set} (A : J -> Setoid') (j : J)
    : SetoidHom (A j) (CoqSetoid_bigCoprodOb A) :=
{
    func := fun x : A j => existT _ j x
}.
Proof. proper. Defined.

#[refine]
Instance CoqSetoid_cotuple {J : Set} {A : J -> Setoid'} {X : Setoid'}
    (f : forall j : J, SetoidHom (A j) X)
    : SetoidHom (CoqSetoid_bigCoprodOb A) X :=
{
    func := fun x => f (projT1 x) (projT2 x)
}.
Proof.
  proper.
  destruct x, y. cbn in *. destruct H; subst. inversion H0.
  apply inj_pair2 in H. subst. rewrite H1. reflexivity.
Defined.

#[refine]
Instance CoqSetoid_has_all_coproducts : has_all_coproducts CoqSetoid :=
{
    bigCoprodOb := @CoqSetoid_bigCoprodOb;
    bigCoproj := @CoqSetoid_bigCoproj;
    cotuple := @CoqSetoid_cotuple
}.
Proof.
  simpl; intros; eauto. setoid.
Defined.

#[refine]
Instance CoqSetoid_expOb_setoid (X Y : Setoid')
    : Setoid (SetoidHom X Y) :=
{
    equiv := fun f g : SetoidHom X Y => forall x : X, f x == g x
}.
Proof. setoid. Defined.

Instance CoqSetoid_expOb (X Y : Setoid') : Setoid' :=
{
    carrier := SetoidHom X Y;
    setoid := CoqSetoid_expOb_setoid X Y
}.

Instance CoqSetoid_eval (X Y : Setoid')
    : SetoidHom (prodOb (CoqSetoid_expOb X Y) X) Y.
Proof.
  split with (fun fx : SetoidHom X Y * X => (fst fx) (snd fx)).
  proper. destruct x, y, H; cbn in *. setoid.
Defined.

Definition CoqSetoid_curry_fun
    (X Y Z : Setoid') (f : SetoidHom (CoqSetoid_prodOb Z X) Y)
    : Z -> (CoqSetoid_expOb X Y).
Proof.
  intro z. destruct f as [f Hf]; do 2 red in Hf; simpl in *.
  split with (fun x : X => f (z, x)). do 2 red. intros.
  apply Hf. cbn; split; [reflexivity | assumption].
Defined.

Instance CoqSetoid_curry
    (X Y Z : Setoid') (f : SetoidHom (CoqSetoid_prodOb Z X) Y)
    : SetoidHom Z (CoqSetoid_expOb X Y).
Proof.
  split with (CoqSetoid_curry_fun f). do 2 red. intros.
  setoidhom f; unfold CoqSetoid_curry_fun; simpl in *. intro x'.
  apply f_pres_equiv. cbn. split; [assumption | reflexivity].
Defined.

#[refine]
Instance CoqSetoid_has_exponentials : has_exponentials CoqSetoid :=
{
    expOb := CoqSetoid_expOb;
    eval := CoqSetoid_eval;
    curry := CoqSetoid_curry
}.
Proof.
  all: red; intros; setoid.
Defined.

Instance CoqSetoid_cartesian_closed : cartesian_closed CoqSetoid :=
{
    ccc_term := CoqSetoid_has_term;
    ccc_prod := CoqSetoid_has_products;
    ccc_exp := CoqSetoid_has_exponentials;
}.

Instance HomFunctor_fob (C : Cat) (X : Ob C)
    : Ob C -> Setoid' := fun Y : Ob C =>
{|
    carrier := Hom X Y;
    setoid := HomSetoid X Y
|}.

Instance HomFunctor_fmap (C : Cat) (X : Ob C)
    : forall Y Z : Ob C, Hom Y Z ->
    SetoidHom (HomFunctor_fob C X Y) (HomFunctor_fob C X Z).
Proof.
  intros Y Z g. split with (fun f : Hom X Y => f .> g).
  proper.
Defined.

#[refine]
Instance HomFunctor (C : Cat) (X : Ob C) : Functor C CoqSetoid :=
{
    fob := HomFunctor_fob C X;
    fmap := HomFunctor_fmap C X;
}.
Proof. proper. all: cat. Defined.