Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".

Require Export Coq.Classes.SetoidClass.

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.
Require Export Equalizer.
Require Export BigProdCoprod.

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
    intro. repeat rewrite H in H1. assumption.
    setoid.
Defined.

(* TODO: There's a problem with the definition of surjectiveS *)
(*Theorem CoqSetoid_ret_char : forall (X Y : Setoid') (f : SetoidHom X Y),
    Ret f <-> surjectiveS f.
Proof.
  unfold Ret, surjectiveS; split; simpl; intros.
    destruct H as [g H]. exists (g b). apply H.
    Lemma l : forall (X Y : Setoid') (f : SetoidHom X Y)
      (H : forall b : Y, exists a : X, f a == b), SetoidHom Y X.
      intros. red. exists (fun y : Y => proj1_sig
      (constructive_indefinite_description _ (H y))).
      proper. do 2 destruct (constructive_indefinite_description _ _);
      simpl. setoid'.
Abort. *)
    

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

Definition CoqSetoid_diag (A B X : Setoid')
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
    diag := CoqSetoid_diag
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

Definition CoqSetoid_codiag (A B X : Setoid')
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
    codiag := CoqSetoid_codiag;
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
      do 2 rewrite Hu'.
      induction H0; subst.
        apply q'_pres_equiv. assumption.
        apply H.
        apply Q'_equiv_sym. assumption.
        eapply Q'_equiv_trans; eauto.
    exists (trick X Y Q' f g q' H). setoid'.
Defined.

Print has_all_products.

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
  red. exists (fun (f : forall j : J, A j) => f j).
  proper. rewrite H. reflexivity.
Defined.

Definition CoqSetoid_bigDiag {J : Set} {A : J -> Setoid'} {X : Setoid'}
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
    bigDiag := @CoqSetoid_bigDiag
}.
Proof.
  simpl; intros; eauto.
  unfold big_product_skolem; red; simpl; split; intros;
  try reflexivity; eauto.
Defined.

Print has_all_coproducts.

Inductive equiv_hetero {A : Type} (S : Setoid A)
    : forall (B : Type), A -> B -> Prop :=
    | equiv_hetero_step : forall x y : A, x == y -> equiv_hetero S A x y.

Hint Constructors equiv_hetero.

(* TODO *)
Instance CoqSetoid_bigCoprodOb {J : Set} (A : J -> Setoid') : Setoid' :=
{
    carrier := {j : J & A j};
    setoid := {| equiv := fun x y : {j : J & A j} =>
      projT1 x = projT1 y /\
      equiv_hetero (A (projT1 x)) (A (projT1 y)) (projT2 x) (projT2 y) |}
}.
Proof.
  split; red; destruct x; try destruct y; try destruct z;
  simpl; intros.
    split; auto. constructor. reflexivity.
    destruct H; subst. split; auto. inversion H0; subst.
      constructor. destruct (existT _ (A x0) y). simpl in *.
    Print sigT.
    Focus 2. destruct H, H0; split.
      rewrite H, H0. auto.
      