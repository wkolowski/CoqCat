From Cat Require Export Cat.

Class HSetoid : Type :=
{
  carrier : Type;
  hequiv : forall {A : Type}, carrier -> A -> Prop;
  hequiv_refl : forall x : carrier, hequiv x x;
  hequiv_sym : forall x y : carrier, hequiv x y -> hequiv y x;
  hequiv_trans : forall x y z : carrier, hequiv x y -> hequiv y z -> hequiv x z
}.

Coercion carrier : HSetoid >-> Sortclass.

Notation "x === y" := (hequiv x y) (at level 40).

#[global] Hint Resolve hequiv_refl hequiv_sym hequiv_trans : core.

Definition HSetoidHom (X Y : HSetoid) : Type :=
  {f : X -> Y | forall x x' : X, x === x' -> f x === f x'}.

Definition HSetoidHom_Fun (X Y : HSetoid) (f : HSetoidHom X Y) : X -> Y := proj1_sig f.
Coercion HSetoidHom_Fun : HSetoidHom >-> Funclass.

#[refine]
#[export]
Instance HSetoidHomSetoid (X Y : HSetoid) : Setoid (HSetoidHom X Y) :=
{
  equiv := fun f g : HSetoidHom X Y => forall x : X, f x === g x
}.
Proof. now solve_equiv. Defined.

Definition HSetoidComp
  (X Y Z : HSetoid) (f : HSetoidHom X Y) (g : HSetoidHom Y Z) : HSetoidHom X Z.
Proof.
  exists (fun x : X => g (f x)).
  intros x1 x2 Heq.
  destruct f as [h Hf], g as [g Hg]; cbn in *.
  now apply Hg, Hf.
Defined.

Definition HSetoidId (X : HSetoid) : HSetoidHom X X.
Proof.
  now exists (fun x : X => x).
Defined.

#[refine]
#[export]
Instance HSetoidCat : Cat :=
{
  Ob := HSetoid;
  Hom := HSetoidHom;
  HomSetoid := HSetoidHomSetoid;
  comp := HSetoidComp;
  id := HSetoidId;
}.
Proof.
  - intros A B C [f1 Hf1] [f2 Hf2] Hf [g1 Hg1] [g2 Hg2] Hg x; cbn in *.
    apply hequiv_trans with (g2 (f1 x)).
    + now apply Hg.
    + now apply Hg2, Hf.
  - easy.
  - easy.
  - easy.
Defined.