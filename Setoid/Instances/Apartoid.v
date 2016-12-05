Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Coq.Classes.SetoidClass.

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Class Apartoid : Type :=
{
    carrier : Type;
    neq : carrier -> carrier -> Prop;
    neq_irrefl : forall x y : carrier, ~ neq x x;
    neq_sym : forall x y : carrier, neq x y -> neq y x;
    weird : forall x y z : carrier, neq x y -> neq z x \/ neq z y
}.

Coercion carrier : Apartoid >-> Sortclass.

Hint Resolve neq_irrefl neq_sym weird.

(*Instance Apartoid_to_Setoid (A : Apartoid) : Setoid A :=
{
    equiv := fun x y : A => ~ neq x y
}.
Proof.
  split; red; intros; intro; eauto.
    eapply neq_irrefl; eauto.
    destruct (weird x z y H1); auto.
Defined.*)

Definition ApartoidHom (X Y : Apartoid) : Type :=
    {f : X -> Y | forall x x' : X, neq x x' -> neq (f x) (f x')}.

Definition ApartoidHom_Fun {X Y : Apartoid} (f : ApartoidHom X Y) : X -> Y
    := proj1_sig f.
Coercion ApartoidHom_Fun : ApartoidHom >-> Funclass.

Definition ApartoidComp (X Y Z : Apartoid) (f : ApartoidHom X Y)
    (g : ApartoidHom Y Z) : ApartoidHom X Z.
Proof.
  red; destruct f as [f Hf], g as [g Hg].
  exists (fun x : X => g (f x)). auto.
Defined.

Definition ApartoidId (X : Apartoid) : ApartoidHom X X.
Proof.
  red. exists (fun x : X => x). auto.
Defined.

Instance ApartoidCat : Cat :=
{
    Ob := Apartoid;
    Hom := ApartoidHom;
    HomSetoid := fun X Y : Apartoid =>
        {| equiv := fun f g : ApartoidHom X Y => forall x : X, f x = g x |};
    comp := ApartoidComp;
    id := ApartoidId
}.
Proof.
  (* Equivalence *) cat. red. intros. rewrite H, H0. auto.
  (* Proper *) repeat red; intros. destruct x, y, x0, y0; simpl in *.
    rewrite H, H0. auto.
  (* Category laws *) all: intros; repeat match goal with
    | f : ApartoidHom _ _ |- _ => destruct f
  end; simpl; auto.
Defined.

Instance Apartoid_init : Apartoid :=
{
    carrier := Empty_set;
    neq := fun (e : Empty_set) _ => match e with end
}.
Proof. all: destruct x. Defined.

Definition Apartoid_create (X : Apartoid) : ApartoidHom Apartoid_init X.
Proof.
  red; simpl. exists (fun (e : Empty_set) => match e with end). destruct x.
Defined.

Instance Apartoid_has_init : has_init ApartoidCat :=
{
    init := Apartoid_init;
    create := Apartoid_create
}.
Proof. cat. Defined.


Instance Apartoid_has_init' : has_init ApartoidCat := {}.
Proof.
  refine {| carrier := Empty_set;
      neq := fun (e : Empty_set) _ => match e with end |}. cat. cat. cat.
  repeat red; simpl in *; intros.
    exists (fun e : Empty_set => match e with end). destruct x.
    cat.
Defined.

Eval cbn in init ApartoidCat.