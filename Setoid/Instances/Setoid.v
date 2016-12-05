Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".

Require Export Cat.
Require Export Coq.Classes.SetoidClass.

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
        {| equiv := fun f g : SetoidHom X Y => forall x : X, f x = g x |};
    comp := SetoidComp;
    id := SetoidId
|}.
Proof.
  (* Equivalence *) cat. red. intros. rewrite H, H0. auto.
  (* Proper *) repeat red. intros. destruct x, y, x0, y0. cat.
    rewrite H, H0. auto.
  (* Category laws *) all: intros; repeat match goal with
    | f : SetoidHom _ _ |- _ => destruct f
  end; simpl; auto.
Defined.