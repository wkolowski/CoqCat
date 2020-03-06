Require Export Cat.

Class HSetoid : Type :=
{
    carrier : Type;
    hequiv : forall {A : Type}, carrier -> A -> Prop;
    hequiv_refl : forall x : carrier,
      hequiv x x;
    hequiv_sym : forall x y : carrier,
      hequiv x y -> hequiv y x;
    hequiv_trans : forall x y z : carrier,
      hequiv x y -> hequiv y z -> hequiv x z
}.

Coercion carrier : HSetoid >-> Sortclass.

Notation "x === y" := (hequiv x y) (at level 40).

Hint Resolve hequiv_refl hequiv_sym hequiv_trans.

Definition HSetoidHom (X Y : HSetoid) : Type :=
    {f : X -> Y | forall x x' : X, x === x' -> f x === f x'}.

Definition HSetoidHom_Fun (X Y : HSetoid) (f : HSetoidHom X Y)
    : X -> Y := proj1_sig f.
Coercion HSetoidHom_Fun : HSetoidHom >-> Funclass.

#[refine]
Instance HSetoidHomSetoid (X Y : HSetoid) : Setoid (HSetoidHom X Y) :=
{
    equiv := fun f g : HSetoidHom X Y =>
      forall x : X, f x === g x
}.
Proof. split; red; intros; eauto. Defined.

Definition HSetoidComp (X Y Z : HSetoid)
    (f : HSetoidHom X Y) (g : HSetoidHom Y Z) : HSetoidHom X Z.
Proof.
  red. exists (fun x : X => g (f x)). intros.
  destruct f, g. simpl. apply h0. apply h. assumption.
Defined.

Definition HSetoidId (X : HSetoid) : HSetoidHom X X.
Proof.
  red. exists (fun x : X => x). intros. assumption.
Defined.

#[refine]
Instance HSetoidCat : Cat :=
{
    Ob := HSetoid;
    Hom := HSetoidHom;
    HomSetoid := HSetoidHomSetoid;
    comp := HSetoidComp;
    id := HSetoidId;
}.
Proof.
  (* Composition is proper *) proper.
    apply hequiv_trans with (y0 (x x1)). apply H0.
    destruct y0; simpl in *. apply h. apply H.
  (* Category laws *) all: cat.
Defined.