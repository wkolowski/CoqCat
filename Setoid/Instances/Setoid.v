Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".

Require Export Coq.Classes.SetoidClass.

Require Export Cat.
Require Export Equalizer.

Class Setoid' : Type :=
{
    carrier :> Type;
    setoid :> Setoid carrier
}.

Coercion carrier : Setoid' >-> Sortclass.

Definition SetoidHom (X Y : Setoid') : Type := {f: X -> Y |
    Proper ((@equiv _ (@setoid X)) ==> (@equiv _ (@setoid Y))) f}.

Definition SetoidHom_Fun (X Y : Setoid') (f : SetoidHom X Y) : X -> Y
    := proj1_sig f.
Coercion SetoidHom_Fun : SetoidHom >-> Funclass.

Definition SetoidComp (X Y Z : Setoid') (f : SetoidHom X Y)
    (g : SetoidHom Y Z) : SetoidHom X Z.
Proof.
  destruct f as [f Hf], g as [g Hg]; red.
  exists (fun x : X => g (f x)). repeat red in Hf, Hg.
  repeat red; destruct X, Y, Z; simpl in *. destruct setoid1, setoid2.
  intros. apply Hg. apply Hf. assumption.
Defined.

Definition SetoidId (X : Setoid') : SetoidHom X X.
Proof.
  exists (fun x : X => x). repeat red. cat.
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
  (* Equivalence *) cat; red; intros; try rewrite H; try rewrite H0;
    try reflexivity.
  (* Proper *) repeat red; intros. destruct A, B, C, x, y, x0, y0.
    destruct setoid0, setoid1, setoid2. simpl in *. rewrite H, H0.
    reflexivity.
  (* Category laws *) all: intros; repeat match goal with
    | f : SetoidHom _ _ |- _ => destruct f
  end; cat.
Defined.

Instance CoqSet_coequalizer_Setoid (X Y : Setoid') (f g : SetoidHom X Y) :
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
  cat; red.
    intro y. right. reflexivity.
    intros y y'; destruct 1 as [[x [eq1 [eq2 eq3]]] | H].
      left. exists x. repeat split. rewrite <- eq3. assumption.
        rewrite eq3. assumption. symmetry. assumption.
      right. symmetry. assumption.
    intros y1 y2 y3; destruct 1 as [[x [eq1 [eq2 eq3]]] | H];
    destruct 1 as [[x' [eq1' [eq2' eq3']]] | H'].
      right. rewrite eq3. assumption.
      left. exists x. split; try rewrite <- H'; auto.
      left. exists x'. split; rewrite H; auto.
      right. rewrite H; auto.
Defined.

Instance CoqSet_coeq_ob (X Y : Setoid') (f g : SetoidHom X Y) :
    Setoid' :=
{
    carrier := Y;
    setoid := CoqSet_coequalizer_Setoid X Y f g 
}.

Definition CoqSet_coeq_mor (X Y : Setoid') (f g : SetoidHom X Y)
    : SetoidHom Y (CoqSet_coeq_ob X Y f g).
Proof.
  red. exists (fun y : Y => y). repeat red; intros.
  right. assumption.
Defined.

Instance CoqSetoid_has_coequalizers : has_coequalizers CoqSetoid :=
{
    coeq_ob := CoqSet_coeq_ob;
    coeq_mor := CoqSet_coeq_mor
}.
Proof.
  unfold coequalizer; split; intros.
    destruct X, Y, f as [f Hf], g as [g Hg]; simpl in *; intro x.
      left. exists x. repeat split; try reflexivity.
      repeat red in p; repeat red in p0.
    Focus 2. 