Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".
Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/Instances".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export Sumprod.

Set Universe Polymorphism.

Instance SetP : Cat :=
{
  Ob := Set;
  Hom := fun X Y : Set => X -> option Y;
  HomSetoid := fun X Y : Set =>
    {| equiv := fun f g : X -> option Y => forall x : X , f x = g x |};
  comp := fun (X Y Z : Set) (f : X -> option Y) (g : Y -> option Z) =>
    fun x : X => match f x with
        | None => None
        | Some y => g y
    end;
  id := fun (X : Set) (x : X) => Some x
}.
Proof.
  (* Equivalence *) cat; red; intros. rewrite H, H0. auto.
  (* Proper *) repeat red; simpl; intros. rewrite H.
    destruct (y x1); auto.
  (* Category laws *) all: cat; try destruct (f x); cat.
Defined.

Instance SetP_has_init : has_init SetP :=
{
    init := Empty_set;
    create := fun (X : Ob SetP) (e : Empty_set) => match e with end
}.
Proof. cat. Defined.

Instance SetP_has_term : has_term SetP :=
{
    term := Empty_set;
    delete := fun (X : Ob SetP) (x : X) => None
}.
Proof. cat; destruct (f x); cat. Defined.

Instance SetP_has_zero : has_zero SetP := {}.
Proof. cat. Defined.

Eval compute in zero_ob SetP.

Definition SetP_proj1 (X Y : Set) (p : sumprod X Y) : option X :=
match p with
    | inl' x => Some x
    | pair' x _ => Some x
    | _ => None
end.

Definition SetP_proj2 (X Y : Set) (p : sumprod X Y) : option Y :=
match p with
    | inr' y => Some y
    | pair' _ y => Some y
    | _ => None
end.

Definition SetP_diag (A B X : Set) (f : Hom X A) (g : Hom X B)
    : Hom X (sumprod A B) := fun x : X =>
match f x, g x with
    | None, None => None
    | Some a, None => Some (inl' a)
    | None, Some b => Some (inr' b)
    | Some a, Some b => Some (pair' a b)
end.

Instance SetP_has_products : has_products SetP :=
{
    prodOb := sumprod;
    proj1 := SetP_proj1;
    proj2 := SetP_proj2;
    diag := SetP_diag
}.
Proof.
  all: unfold SetP_diag; repeat (red || split); simpl; intros; cat.
    rewrite H, H0. auto.
    destruct (f x), (g x); auto.
    destruct (f x), (g x); auto.
    rewrite H, H0; destruct (y x); try destruct s; auto.
Defined.

Definition SetP_codiag (A B X : Ob SetP) (f : Hom A X) (g : Hom B X)
    : Hom (sum A B) X := fun p : A + B =>
match p with
    | inl a => f a
    | inr b => g b
end.

Instance SetP_has_coproducts : has_coproducts SetP :=
{
    coprodOb := sum;
    coproj1 := fun (A B : Set) (a : A) => Some (inl a);
    coproj2 := fun (A B : Set) (b : B) => Some (inr b);
    codiag := SetP_codiag
}.
Proof.
  repeat red; simpl; intros. unfold SetP_codiag.
    destruct x1; try rewrite H; try rewrite H0; auto.
  cat. destruct x; cat.
Defined.