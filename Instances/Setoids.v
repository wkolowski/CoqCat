Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.
Require Export Equalizer.
Require Export BigProdCoprod.
Require Import Exponential.
Require Import CartesianClosed.

Require Import Functor.

Set Implicit Arguments.

Class Setoid' : Type :=
{
    carrier :> Type;
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

Definition SetoidHom (X Y : Setoid') : Type := {f : X -> Y |
    Proper ((@equiv _ (@setoid X)) ==> (@equiv _ (@setoid Y))) f}.

Definition SetoidHom_Fun (X Y : Setoid') (f : SetoidHom X Y) : X -> Y
    := proj1_sig f.
Coercion SetoidHom_Fun : SetoidHom >-> Funclass.

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

Ltac setoid' := repeat (setoid_simpl || cat || setoidhoms || setoidobs).
Ltac setoid := try (setoid'; fail).

Definition SetoidComp (X Y Z : Setoid') (f : SetoidHom X Y)
    (g : SetoidHom Y Z) : SetoidHom X Z.
Proof.
  setoid. exists (fun x : X => g (f x)). setoid.
Defined.

Definition SetoidId (X : Setoid') : SetoidHom X X.
Proof.
  setoid_simpl. exists (fun x : X => x). setoid.
Defined.

Instance CoqSetoid : Cat :=
{|
    Ob := Setoid';
    Hom := SetoidHom;
    HomSetoid := fun X Y : Setoid' =>
      {| equiv := fun f g : SetoidHom X Y =>
        forall x : X, @equiv _ (@setoid Y) (f x) (g x) |};
    comp := SetoidComp;
    id := SetoidId
|}.
Proof.
  (* Equivalence *) solve_equiv.
  (* Proper *) setoid.
  (* Category laws *) all: setoid.
Restart.
  all: try solve_equiv; setoid. (* Faster than just setoid *)
Defined.

Theorem CoqSetoid_mon_char : forall (X Y : Setoid') (f : SetoidHom X Y),
    Mon f <-> injectiveS f.
Proof.
  Lemma g1 : forall (X Y : Setoid') (y : Y), SetoidHom X Y.
    Proof. intros. red. exists (fun _ => y). proper. Defined.
  unfold Mon, injectiveS; split; intros.
    specialize (H _ (g1 Y X a) (g1 Y X a')). simpl in H.
      apply H; auto. exact (f a).
    simpl. intro. apply H. apply H0.
Defined.

Theorem CoqSetoid_sur_is_epi : forall (X Y : Setoid') (f : SetoidHom X Y),
    surjectiveS f -> Epi f.
Proof.
  unfold Epi, surjectiveS; intros. simpl in *. intro.
  destruct (H x) as [a eq]. setoid'. pose (eq' := eq).
  apply g_pres_equiv in eq'. apply h_pres_equiv in eq.
  do 2 eapply X0_equiv_trans; eauto.
Defined.

Theorem CoqSetoid_sec_is_inj : forall (X Y : Setoid') (f : SetoidHom X Y),
    Sec f -> injectiveS f.
Proof.
  unfold Sec, injectiveS; intros.
  destruct H as [g H]. simpl in *. cut (g (f a) == g (f a')).
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
    do 2 destruct H. exists (exist _ _ H). cat.
Qed.

Instance CoqSetoid_init : Setoid' :=
{
    carrier := Empty_set;
    setoid := {| equiv := fun (x y : Empty_set) => match x with end |}
}.
Proof. solve_equiv. Defined.

Definition CoqSetoid_create (X : Setoid') : SetoidHom CoqSetoid_init X.
Proof.
  red. exists (fun e : Empty_set => match e with end). setoid.
Defined.

Instance CoqSetoid_has_init : has_init CoqSetoid :=
{
    init := CoqSetoid_init;
    create := CoqSetoid_create;
}.
Proof. setoid'. Defined.

Instance CoqSetoid_term : Setoid' :=
{
    carrier := unit;
    setoid := {| equiv := fun _ _ => True |};
}.
Proof. solve_equiv. Defined.

Definition CoqSetoid_delete (X : Setoid') : SetoidHom X CoqSetoid_term.
Proof.
  red. exists (fun _ => tt). setoid.
Defined.

Instance CoqSetoid_has_term : has_term CoqSetoid :=
{
    term := CoqSetoid_term;
    delete := CoqSetoid_delete;
}.
Proof. setoid. Defined.

Instance CoqSetoid_prodOb (X Y : Setoid') : Setoid' :=
{
    carrier := X * Y;
    setoid := {| equiv := fun p1 p2 : X * Y =>
      @equiv _ (@setoid X) (fst p1) (fst p2) /\
      @equiv _ (@setoid Y) (snd p1) (snd p2) |}
}.
Proof. solve_equiv. Defined.

Definition CoqSetoid_proj1 (X Y : Setoid')
    : SetoidHom (CoqSetoid_prodOb X Y) X.
Proof.
  red. exists fst. setoid'.
Defined.

Definition CoqSetoid_proj2 (X Y : Setoid')
    : SetoidHom (CoqSetoid_prodOb X Y) Y.
Proof.
  red. exists snd. setoid'.
Defined.

Definition CoqSetoid_fpair (A B X : Setoid')
    (f : SetoidHom X A) (g : SetoidHom X B)
    : SetoidHom X (CoqSetoid_prodOb A B).
Proof.
  red. exists (fun x : X => (f x, g x)). setoid'.
Defined.

Instance CoqSetoid_has_products : has_products CoqSetoid :=
{
    prodOb := CoqSetoid_prodOb;
    proj1 := CoqSetoid_proj1;
    proj2 := CoqSetoid_proj2;
    fpair := CoqSetoid_fpair
}.
Proof. all: setoid'. Defined.

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

Definition CoqSetoid_coproj1 (X Y : Setoid')
    : SetoidHom X (CoqSetoid_coprodOb X Y).
Proof.
  red. exists inl. proper.
Defined.

Definition CoqSetoid_coproj2 (X Y : Setoid')
    : SetoidHom Y (CoqSetoid_coprodOb X Y).
Proof.
  red. exists inr. proper.
Defined.

Definition CoqSetoid_copair (A B X : Setoid')
    (f : SetoidHom A X) (g : SetoidHom B X)
    : SetoidHom (CoqSetoid_coprodOb A B) X.
Proof.
  red. exists (fun p : sum A B =>
  match p with
    | inl a => f a
    | inr b => g b
  end).
  proper. destruct x, y; setoid.
Defined.

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
Defined.

Instance CoqSetoid_eq_ob {X Y : Setoid'} (f g : SetoidHom X Y)
    : Setoid' :=
{
    carrier := {x : X | f x == g x};
    setoid := {| equiv := fun p1 p2 =>
      @equiv _ (@setoid X) (proj1_sig p1) (proj1_sig p2) |}
}.
Proof.
  setoid'; destruct H; try destruct H0; eauto.
Defined.

Definition CoqSetoid_eq_mor {X Y : Setoid'} (f g : SetoidHom X Y)
    : SetoidHom (CoqSetoid_eq_ob f g) X.
Proof.
  red. unfold CoqSetoid_eq_ob; simpl in *.
  exists (@proj1_sig _ _). proper.
Defined.

Lemma trick_eq {X Y E' : Setoid'} (f g : SetoidHom X Y)
    (e' : SetoidHom E' X) (H : forall x : E', f (e' x) == g (e' x))
    : E' -> CoqSetoid_eq_ob f g.
Proof.
  intro arg. setoidhom e'; simpl in *. exists (e' arg). apply H.
Defined.

Lemma trick_eq' {X Y E' : Setoid'} (f g : SetoidHom X Y)
    (e' : SetoidHom E' X) (H : forall x : E', f (e' x) == g (e' x))
    : SetoidHom E' (CoqSetoid_eq_ob f g).
Proof.
  red. exists (trick_eq f g e' H). do 2 red. intros.
  unfold trick_eq. simpl. setoid'.
Defined.

Instance CoqSetoid_has_equalizers : has_equalizers CoqSetoid :=
{
    eq_ob := @CoqSetoid_eq_ob;
    eq_mor := @CoqSetoid_eq_mor;
}.
Proof.
  repeat (red || split).
    destruct x. auto.
    intros. exists (trick_eq' f g e' H). setoid'.
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

Instance CoqSetoid_coeq_ob {X Y : Setoid'} (f g : SetoidHom X Y) :
    Setoid' :=
{
    carrier := Y;
    setoid :=
      {| equiv := CoqSetoid_coeq_equiv f g |}
}.
Proof.
  repeat (red || split).
    intro y. constructor. reflexivity.
    intros y y' H. apply coeq_sym. assumption.
    intros y1 y2 y3 H1 H2. eapply coeq_trans; eauto.
Defined.

Definition CoqSetoid_coeq_mor (X Y : Setoid') (f g : SetoidHom X Y)
    : Hom Y (CoqSetoid_coeq_ob f g).
Proof.
  repeat red. unfold CoqSetoid_coeq_ob; simpl in *.
  exists (fun y : Y => y). repeat red. intros. constructor. assumption.
Defined.

Lemma trick (X Y Q' : Setoid') (f g : SetoidHom X Y)
    (q' : SetoidHom Y Q') (H : forall x : X, q' (f x) == q' (g x))
    : SetoidHom (CoqSetoid_coeq_ob f g) Q'.
Proof.
  red. exists q'. proper. induction H0; subst; setoid'.
Defined.

Instance CoqSetoid_has_coequalizers : has_coequalizers CoqSetoid :=
{
    coeq_ob := @CoqSetoid_coeq_ob;
    coeq_mor := CoqSetoid_coeq_mor
}.
Proof.
  setoid_simpl.
    apply coeq_quot.
    assert (u' : {u : SetoidHom Y Q' |
      forall y : Y, u y = q' y}).
      exists q'. reflexivity.
    assert (u : SetoidHom (CoqSetoid_coeq_ob f g) Q').
      red. exists (proj1_sig u'). proper. destruct u' as [u' Hu'].
      setoidhom q'; setoidhom u'; setoidob Q'; simpl in *.
      rewrite !Hu'.
      induction H0; subst.
        apply q'_pres_equiv. assumption.
        apply H.
        apply Q'_equiv_sym. assumption.
        eapply Q'_equiv_trans; eauto.
    exists (trick f g q' H). setoid'.
Defined.

Instance CoqSetoid_bigProdOb {J : Set} (A : J -> Setoid') : Setoid' :=
{
    carrier := forall j : J, A j;
    setoid := {| equiv := fun f g : forall j : J, A j =>
      forall j : J, @equiv _ (A j) (f j) (g j) |}
}.
Proof.
  split; red; intros; try rewrite H; try rewrite H0; reflexivity.
Defined.

Definition CoqSetoid_bigProj {J : Set} (A : J -> Setoid') (j : J)
    : SetoidHom (CoqSetoid_bigProdOb A) (A j).
Proof.
  red. exists (fun (f : forall j : J, A j) => f j). proper.
Defined.

Definition CoqSetoid_tuple {J : Set} {A : J -> Setoid'} {X : Setoid'}
    (f : forall j : J, SetoidHom X (A j))
    : SetoidHom X (CoqSetoid_bigProdOb A).
Proof.
  red. exists (fun x : X => (fun j : J => f j x)).
  do 2 red; simpl; intros. destruct (f j) as [g g_proper];
  do 2 red in g_proper; simpl. apply g_proper. assumption.
Defined.

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
  intros. Check JMeq_eq. Require Import Program. subst.
  apply JMeq_eq in H0. subst. dependent destruction H1.
  dependent destruction H2. constructor. rewrite H. assumption.
Qed.

Arguments equiv_hetero_trans [A B C SA SB x y z] _ _ _ _.

Instance CoqSetoid_bigCoprodOb {J : Set} (A : J -> Setoid') : Setoid' :=
{
    carrier := {j : J & A j};
    setoid := {| equiv := fun x y : {j : J & A j} =>
      projT1 x = projT1 y /\
      equiv_hetero (A (projT1 x)) (projT2 x) (projT2 y) |}
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

Instance CoqSetoid_expOb_setoid (X Y : Setoid')
    : Setoid (SetoidHom X Y) :=
{
    equiv := fun f g : SetoidHom X Y => forall x : X, f x == g x
    (*equiv := fun f g : X -> Y =>
        forall x x' : X, x == x' -> f x == g x'*)
}.
Proof.
  solve_equiv.
Defined.

Instance CoqSetoid_expOb (X Y : Setoid') : Setoid' :=
{
    carrier := SetoidHom X Y;
    setoid := CoqSetoid_expOb_setoid X Y
}.

Definition CoqSetoid_eval (X Y : Setoid')
    : SetoidHom (prodOb (CoqSetoid_expOb X Y) X) Y.
Proof.
  red; simpl. exists (fun fx : SetoidHom X Y * X => (fst fx) (snd fx)).
  proper. destruct x, y, H; simpl in *. setoid.
Defined.

Definition CoqSetoid_curry_fun
    (X Y Z : Setoid') (f : SetoidHom (CoqSetoid_prodOb Z X) Y)
    : Z -> (CoqSetoid_expOb X Y).
Proof.
  intro z; do 3 red. destruct f as [f Hf]; do 2 red in Hf; simpl in *.
  exists (fun x : X => f (z, x)). do 2 red. intros.
  apply Hf. simpl. split; [reflexivity | assumption].
Defined.

Definition CoqSetoid_curry
    (X Y Z : Setoid') (f : SetoidHom (CoqSetoid_prodOb Z X) Y)
    : SetoidHom Z (CoqSetoid_expOb X Y).
Proof.
  exists (CoqSetoid_curry_fun f). do 2 red. intros.
  setoidhom f; unfold CoqSetoid_curry_fun; simpl in *. intro x'.
  apply f_pres_equiv. simpl. split; [assumption | reflexivity].
Defined.

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

Definition HomFunctor_fmap (C : Cat) (X : Ob C)
    : forall Y Z : Ob C, Hom Y Z ->
    SetoidHom (HomFunctor_fob C X Y) (HomFunctor_fob C X Z).
Proof.
  intros Y Z g. red; simpl.
  exists (fun f : Hom X Y => f .> g).
  proper.
Defined.

Instance HomFunctor (C : Cat) (X : Ob C) : Functor C CoqSetoid :=
{
    fob := HomFunctor_fob C X;
    fmap := HomFunctor_fmap C X;
}.
Proof. proper. all: cat. Defined.