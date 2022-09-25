From Cat Require Export Cat.
From Cat.Universal Require Import Initial Terminal Zero Product Coproduct.

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
  - now solve_equiv.
  - intros A B C f1 f2 Hf g1 g2 Hg x; cbn in *.
    rewrite Hf.
    now destruct (f2 x).
  - intros A B C D f g h x.
    now destruct (f x).
  - easy.
  - intros A B f x.
    now destruct (f x).
Defined.

#[refine]
#[export]
Instance HasInit_SetP : HasInit SetP :=
{
  init := Empty_set;
  create := fun (X : Ob SetP) (e : Empty_set) => match e with end
}.
Proof. now intros X f g []. Defined.

#[refine]
#[export]
Instance HasTerm_SetP : HasTerm SetP :=
{
  term := Empty_set;
  delete := fun (X : Ob SetP) (x : X) => None
}.
Proof. now intros X f g x; destruct (f x), (g x). Defined.

#[refine]
#[export]
Instance HasZero_SetP : HasZero SetP := {}.
Proof. easy. Defined.

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
  product := sumprod;
  outl := SetP_outl;
  outr := SetP_outr;
  fpair := SetP_fpair;
}.
Proof.
  split; unfold SetP_fpair; cbn; intros X f g.
  - now intros x; destruct (f x), (g x); cbn.
  - now intros x; destruct (f x), (g x); cbn.
  - intros Heq1 Heq2 x.
    specialize (Heq1 x); specialize (Heq2 x).
    unfold SetP_outl, SetP_outr in *.
    now destruct (f x) as [[] |], (g x) as [[] |]; congruence.
Defined.

Definition SetP_copair
  (A B X : Ob SetP) (f : Hom A X) (g : Hom B X) (p : A + B) : option X :=
match p with
| inl a => f a
| inr b => g b
end.

#[refine]
#[export]
Instance HasCoproducts_SetP : HasCoproducts SetP :=
{
  coproduct := sum;
  finl := fun (A B : Set) (a : A) => Some (inl a);
  finr := fun (A B : Set) (b : B) => Some (inr b);
  copair := SetP_copair
}.
Proof.
  split; unfold SetP_copair; cbn; [easy | easy |].
  now intros P' h1 h2 Heq1 Heq2 [a | b].
Defined.