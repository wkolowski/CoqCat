From Cat Require Export Cat.
From Cat.Limits Require Import Initial Terminal Zero Product Coproduct.

#[refine]
#[export]
Instance SetP : Cat :=
{
  Ob := Set;
  Hom := fun X Y : Set => X -> option Y;
  HomSetoid := fun X Y : Set =>
  {|
    equiv := fun f g : X -> option Y => forall x : X , f x = g x
  |};
  comp := fun (X Y Z : Set) (f : X -> option Y) (g : Y -> option Z) => fun x : X =>
    match f x with
    | None => None
    | Some y => g y
    end;
  id := fun (X : Set) (x : X) => Some x
}.
Proof.
  (* Equivalence *) solve_equiv.
  (* Proper *) proper. rewrite H. destruct (y x1); auto.
  (* Category laws *) all: cat; try destruct (f x); cat.
Defined.

#[refine]
#[export]
Instance HasInit_SetP : HasInit SetP :=
{
  init := Empty_set;
  create := fun (X : Ob SetP) (e : Empty_set) => match e with end
}.
Proof. cat. Defined.

#[refine]
#[export]
Instance HasTerm_SetP : HasTerm SetP :=
{
  term := Empty_set;
  delete := fun (X : Ob SetP) (x : X) => None
}.
Proof. cat; destruct (f x); cat. Defined.

#[refine]
#[export]
Instance HasZero_SetP : HasZero SetP := {}.
Proof. cat. Defined.

Definition SetP_outl (X Y : Set) (p : sumprod X Y) : option X :=
match p with
| inl' x => Some x
| pair' x _ => Some x
| _ => None
end.

Definition SetP_outr (X Y : Set) (p : sumprod X Y) : option Y :=
match p with
| inr' y => Some y
| pair' _ y => Some y
| _ => None
end.

Definition SetP_fpair
  (A B X : Set) (f : Hom X A) (g : Hom X B) : Hom X (sumprod A B) := fun x : X =>
match f x, g x with
| None, None => None
| Some a, None => Some (inl' a)
| None, Some b => Some (inr' b)
| Some a, Some b => Some (pair' a b)
end.

#[refine]
#[export]
Instance HasProducts_SetP : HasProducts SetP :=
{
  prodOb := sumprod;
  outl := SetP_outl;
  outr := SetP_outr;
  fpair := SetP_fpair
}.
Proof.
  all: unfold SetP_fpair; repeat (red || split); cbn; intros; cat.
    rewrite H, H0. auto.
    destruct (f x), (g x); auto.
    destruct (f x), (g x); auto.
    rewrite H, H0; destruct (y x); try destruct s; auto.
Defined.

Definition SetP_copair
  (A B X : Ob SetP) (f : Hom A X) (g : Hom B X) : Hom (sum A B) X := fun p : A + B =>
match p with
| inl a => f a
| inr b => g b
end.

#[refine]
#[export]
Instance HasCoproducts_SetP : HasCoproducts SetP :=
{
  coprodOb := sum;
  finl := fun (A B : Set) (a : A) => Some (inl a);
  finr := fun (A B : Set) (b : B) => Some (inr b);
  copair := SetP_copair
}.
Proof.
  (* codiag is proper *) proper. unfold SetP_copair.
    destruct x1; try rewrite H; try rewrite H0; auto.
  (* Coproduct laws *) red; cat; destruct x; cat.
Defined.