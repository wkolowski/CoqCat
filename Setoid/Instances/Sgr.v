Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".
Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/Instances".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export Sumprod.

Set Universe Polymorphism.

Class Sgr : Type :=
{
    carrier : Type;
    op : carrier -> carrier -> carrier;
    assoc : forall x y z : carrier, op x (op y z) = op (op x y) z
}.

Ltac sgr_assoc := repeat rewrite assoc.
Ltac sgr := sgr_assoc; eauto.

Coercion carrier : Sgr >-> Sortclass.

Definition SgrHom (A B : Sgr) : Type :=
    {f : A -> B | forall x y : A, f (op x y) = op (f x) (f y)}.

Definition SgrHom_Fun (A B : Sgr) (f : SgrHom A B) : A -> B := proj1_sig f.
Coercion SgrHom_Fun : SgrHom >-> Funclass.

Definition SgrComp (A B C : Sgr) (f : SgrHom A B) (g : SgrHom B C)
    : SgrHom A C.
Proof.
  red. destruct f as [f Hf], g as [g Hg].
  exists (fun a : A => g (f a)). intros. rewrite Hf, Hg. auto.
Defined.

Definition SgrId (A : Sgr) : SgrHom A A.
Proof. red. exists (fun a : A => a). auto. Defined.

Instance SgrCat : Cat :=
{
    Ob := Sgr;
    Hom := SgrHom;
    HomSetoid := fun X Y : Sgr =>
        {| equiv := fun f g : SgrHom X Y => forall x : X, f x = g x |};
    comp := SgrComp;
    id := SgrId
}.
Proof.
  (* Equivalence *) cat. red. intros. rewrite H, H0. auto.
  (* Proper *) repeat red; intros. destruct x, y, x0, y0; cat.
    rewrite H, H0. auto.
  (* Category laws *) all: intros; repeat match goal with
    | f : SgrHom _ _ |- _ => destruct f
  end; simpl; auto.
Defined.

Instance Sgr_init : Sgr :=
{
    carrier := Empty_set;
    op := fun (e : Empty_set) _ => match e with end
}.
Proof. cat. Defined.

Definition Sgr_create (X : Sgr) : Hom Sgr_init X.
Proof.
  repeat red. exists (fun e : Sgr_init => match e with end). cat.
Defined.

Instance Sgr_has_init : has_init SgrCat :=
{
    init := Sgr_init;
    create := Sgr_create
}.
Proof. cat. Defined.

Instance Sgr_term : Sgr :=
{
    carrier := unit;
    op := fun _ _ => tt
}.
Proof. cat. Defined.

Definition Sgr_delete (X : Sgr) : Hom X Sgr_term.
Proof.
  repeat red; simpl. exists (fun _ => tt). auto.
Defined.

Instance Sgr_has_term : has_term SgrCat :=
{
    term := Sgr_term;
    delete := Sgr_delete
}.
Proof. cat. Defined.

Instance Sgr_prod (X Y : Sgr) : Sgr := {}.
Proof.
  exact (prod X Y).
  destruct 1, 1. exact (op c c1, op c0 c2).
  destruct x, y, z. sgr.
Defined.

Definition Sgr_proj1 (X Y : Sgr) : SgrHom (Sgr_prod X Y) X.
Proof.
  repeat red. exists fst. destruct x, y. sgr.
Defined.

Definition Sgr_proj2 (X Y : Sgr) : SgrHom (Sgr_prod X Y) Y.
Proof.
  repeat red. exists snd. destruct x, y. sgr.
Defined.

Definition Sgr_diag (X Y Z : Sgr) (f : SgrHom X Y) (g : SgrHom X Z)
    : SgrHom X (Sgr_prod Y Z).
Proof.
  red. exists (fun x : X => (f x, g x)).
  destruct f as [f Hf], g as [g Hg]; simpl in *.
  intros. rewrite Hf, Hg. auto.
Defined.

Instance Sgr_has_products : has_products SgrCat :=
{
    prod' := Sgr_prod;
    proj1' := Sgr_proj1;
    proj2' := Sgr_proj2
}.
Proof.
  repeat red; simpl; intros. exists (Sgr_diag X A B f g).
  cat. destruct f as [f Hf], g as [g Hg], y as [y Hy]; simpl in *.
  rewrite H, H0. destruct (y x). auto.
Defined.

Instance Sgr_coprod (X Y : Sgr) : Sgr :=
{
    carrier := sum X Y;
}.
Proof.
  destruct 1 as [x | y], 1 as [x' | y'].
    left. exact (op x x').
    left. exact x.
    left. exact x'. (*left. exact x'.*)
    right. exact (op y y').
  destruct x, y, z; sgr.
Defined.

Definition Sgr_coproj1 (X Y : Sgr) : SgrHom X (Sgr_coprod X Y).
Proof. red. exists inl. sgr. Defined.

Definition Sgr_coproj2 (X Y : Sgr) : SgrHom Y (Sgr_coprod X Y).
Proof. red. exists inr. sgr. Defined.

(*Definition Sgr_codiag (X Y Z : Sgr) (f : SgrHom X Z) (g : SgrHom Y Z)
    : SgrHom (Sgr_coprod X Y) Z.
Proof.
  repeat red. exists (fun p : X + Y =>
  match p with
    | inl x => f x
    | inr y => g y
  end); destruct x, y, f, g; simpl; auto.

Instance Sgr_has_coproducts : has_coproducts SgrCat :=
{
    coprod := Sgr_coprod;
    coproj1 := Sgr_coproj1;
    coproj2 := Sgr_coproj2
}.
Proof.
  repeat red. destruct f as [f Hf], g as [g Hg]. simpl.*)


Instance Sgr_sumprod (X Y : Sgr) : Sgr :=
{
    carrier := sumprod X Y;
}.
Proof.
  destruct 1 as [x | y | x y], 1 as [x' | y' | x' y'].
    exact (inl' (op x x')).
    exact (pair' x y').
    exact (pair' (op x x') y').
    exact (pair' x' y).
    exact (inr' (op y y')).
    exact (pair' x' (op y y')).
    exact (pair' (op x x') y).
    exact (pair' x (op y y')).
    exact (pair' (op x x') (op y y')).
  destruct x, y, z; sgr.
Defined.

Definition Sgr_coproj1' (X Y : Sgr) : SgrHom X (Sgr_sumprod X Y).
Proof. red. exists (@inl' X Y). sgr. Defined.

Definition Sgr_coproj2' (X Y : Sgr) : SgrHom Y (Sgr_sumprod X Y).
Proof. red. exists (@inr' X Y). sgr. Defined.

(*Definition Sgr_codiag' (X Y Z : Sgr) (f : SgrHom X Z) (g : SgrHom Y Z)
    : SgrHom (Sgr_sumprod X Y) Z.
Proof.
  red. exists (fun p : sumprod X Y =>
  match p with
    | inl' x => f x
    | inr' y => g y
    | pair' x y => op (g y) (f x)
  end).
  destruct x, y, f as [f Hf], g as [g Hg]; simpl in *.
    sgr.
    sgr.
    rewrite Hf. sgr.
    Focus 2. sgr.
    Focus 2. rewrite Hg. sgr.
    
  repeat rewrite Hf; repeat rewrite Hg; sgr.
    rewrite Hf. auto.*)