Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".

Require Export Coq.Classes.SetoidClass.

Require Export Cat.
Require Export Equalizer.

Class Setoid' : Type :=
{
    carrier :> Type;
    setoid :> Setoid carrier
}.
Print Setoid. Print Equivalence.
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

Coercion carrier : Setoid' >-> Sortclass.

Definition SetoidHom (X Y : Setoid') : Type := {f: X -> Y |
    Proper ((@equiv _ (@setoid X)) ==> (@equiv _ (@setoid Y))) f}.

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

Definition SetoidHom_Fun (X Y : Setoid') (f : SetoidHom X Y) : X -> Y
    := proj1_sig f.
Coercion SetoidHom_Fun : SetoidHom >-> Funclass.

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
  (* Equivalence *) setoid.
  (* Proper *) setoid.
  (* Category laws *) all: setoid.
Restart.
  all: setoid.
Defined.

Instance CoqSetoid_coequalizer_Setoid (X Y : Setoid') (f g : SetoidHom X Y) :
    Setoid Y :=
{
    equiv := fun y y' : Y =>
      (exists x : X,
        @equiv _ (@setoid Y) (f x) y /\
        @equiv _ (@setoid Y) (g x) y' /\
        @equiv _ (@setoid Y) y y')
      \/
      @equiv _ (@setoid Y) y y'
}.
Proof.
  setoid_simpl.
    right. reflexivity.
    rename x into y'. destruct H as [[x [eq1 [eq2 eq3]]] | H].
      left. exists x. repeat split. rewrite <- eq3. assumption.
        rewrite eq3. assumption. symmetry. assumption.
      right. symmetry. assumption.
    rename x into y2; rename z into y3;
    destruct H as [[x [eq1 [eq2 eq3]]] | H];
    destruct H0 as [[x' [eq1' [eq2' eq3']]] | H'].
      right. rewrite eq3. assumption.
      left. exists x. split; try rewrite <- H'; auto.
      left. exists x'. split; rewrite H; auto.
      right. rewrite H; auto.
Restart.
  setoid_simpl; try destruct H; try destruct H0; setoid.
Defined.

Instance CoqSetoid_coeq_ob (X Y : Setoid') (f g : SetoidHom X Y) :
    Setoid' :=
{
    carrier := Y;
    setoid := CoqSetoid_coequalizer_Setoid X Y f g 
}.

Definition CoqSetoid_coeq_mor (X Y : Setoid') (f g : SetoidHom X Y)
    : SetoidHom Y (CoqSetoid_coeq_ob X Y f g).
Proof.
  setoid_simpl. exists (fun y : Y => y). setoid.
Defined.

Instance CoqSetoid_has_coequalizers : has_coequalizers CoqSetoid :=
{
    coeq_ob := CoqSetoid_coeq_ob;
    coeq_mor := CoqSetoid_coeq_mor
}.
Proof. (* TODO *)