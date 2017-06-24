Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import NPeano.
Require Import Omega.

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Require Import Cat.Instances.Setoids.

Class Pros : Type :=
{
    carrier : Setoid';
    leq : carrier -> carrier -> Prop;
    leq_Proper : Proper (equiv ==> equiv ==> equiv) leq;
    leq_refl : forall a b : carrier, a == b -> leq a b;
    leq_trans : forall a b c : carrier, leq a b -> leq b c -> leq a c
}.

Notation "x ≤ y" := (leq x y) (at level 40).

Hint Resolve leq_refl leq_trans.

Coercion carrier : Pros >-> Setoid'.

Ltac pros_simpl := repeat (simpl in * || red || split).

Ltac prosob P := try intros until P;
match type of P with
  | Pros =>
    let a := fresh P "_leq" in
    let b := fresh P "_leq_refl" in
    let c := fresh P "_leq_trans" in destruct P as [P a b c]
  | Ob _ => progress simpl in P; prosob P
end; simpl in *.

Ltac prosobs := intros; repeat
match goal with
  | P : Pros |- _ => prosob P
  | X : Ob _ |- _ => prosob X
end.

Definition ProsHom (A B : Pros) : Type :=
    {f : SetoidHom A B| forall a a', a ≤ a' -> f a ≤ f a'}.

Definition ProsHom_Fun {A B : Pros} (f : ProsHom A B)
    : SetoidHom A B := proj1_sig f.
Coercion ProsHom_Fun : ProsHom >-> SetoidHom.

Ltac proshom f := try intros until f;
match type of f with
  | ProsHom _ _ =>
    let a := fresh f "_pres_leq" in destruct f as [f a]
(* TODO        let x := fresh f "_Proper" in pose *)
  | Hom _ _ => progress simpl in f; proshom f
end; simpl in *.

Ltac proshoms := intros; repeat
match goal with
  | f : ProsHom _ _ |- _ => proshom f; setoidhom f
  | f : Hom _ _ |- _ => proshom f
end.

Ltac pros' := repeat (pros_simpl || proshoms || prosobs || cat || omega).
Ltac pros := try (pros'; fail).

Definition ProsComp (A B C : Pros) (f : ProsHom A B) (g : ProsHom B C)
    : ProsHom A C.
Proof.
  red. exists (SetoidComp f g). pros.
Defined.

Definition ProsId (A : Pros) : ProsHom A A.
Proof.
  red. exists (@SetoidId A). pros.
Defined.

Instance ProsCat : Cat :=
{
    Ob := Pros;
    Hom := ProsHom;
    HomSetoid := fun A B : Pros =>
      {| equiv := fun f g : ProsHom A B =>
          forall x : A, @equiv _ B (f x) (g x)
      |};
    comp := ProsComp;
    id := ProsId
}.
Proof.
  (* Equivalence *) solve_equiv.
  (* Proper *) proper. pros'; setoid'.
  (* Category laws *) all: pros.
Defined.

(*Theorem Pros_mon_inj : forall (X Y : Pros) (f : ProsHom X Y),
    Mon f <-> injectiveS f.
Proof.
  unfold Mon, injective; split; red; intros.
    simpl in H. 
    specialize (H NatLe (const _ _ x) (const _ _ y)).
      proshoms. apply H; auto. exact 0.
    simpl. intro. apply H. proshoms. auto.
Defined.

Theorem Pros_epi_sur : forall (X Y : Pros) (f : ProsHom X Y),
    Epi f <-> surjective f.
Proof.
  unfold Epi, surjective; split; intros.
    specialize (H Y (@id ProsCat Y) (const _ _ b)).
    proshoms.
  Focus 2.
    proshoms. intro. destruct (H x). rewrite <- H1. auto.
Abort.

Theorem Pros_sec_inj : forall (X Y : Pros) (f : ProsHom X Y),
    Sec f <-> injective f.
Proof.
  unfold Sec, injective; split; intros.
    destruct H as [g g_inv]. proshoms.
      replace x with (g (f x)); auto.
      replace y with (g (f y)); auto.
      rewrite H0. auto.
Abort.*)

Instance Pros_init : Pros :=
{
    carrier := CoqSetoid_init;
    leq := fun (x y : Empty_set) => match x with end
}.
Proof. all: destruct a. Defined.

Definition Pros_create (X : Pros) : ProsHom Pros_init X.
Proof.
  red. exists (CoqSetoid_create X). pros.
Defined.

Instance Pros_has_init : has_init ProsCat :=
{
    init := Pros_init;
    create := Pros_create
}.
Proof. pros. Defined.

Instance Pros_term : Pros :=
{
    carrier := CoqSetoid_term;
    leq := fun _ _ => True
}.
Proof. all: pros. Defined.

Definition Pros_delete (X : Pros) : ProsHom X Pros_term.
Proof.
  red. exists (CoqSetoid_delete X). pros.
Defined.

Instance Pros_has_term : has_term ProsCat :=
{
    term := Pros_term;
    delete := Pros_delete
}.
Proof. pros. Defined.

Instance Pros_prodOb (X Y : Pros) : Pros :=
{
    carrier := CoqSetoid_prodOb X Y;
    leq := fun x y : X * Y => leq (fst x) (fst y) /\ leq (snd x) (snd y)
}.
Proof.
  proper. destruct H, H0. pose (@leq_Proper X). pose (@leq_Proper Y).
    rewrite H, H0, H1, H2. reflexivity.
  all: pros.
Defined.

Definition Pros_proj1 (X Y : Pros) : ProsHom (Pros_prodOb X Y) X.
Proof.
  red. exists (CoqSetoid_proj1 X Y). pros. Defined.

Definition Pros_proj2 (X Y : Pros) : ProsHom (Pros_prodOb X Y) Y.
Proof.
  red. exists (CoqSetoid_proj2 X Y). pros. Defined.

Definition Pros_fpair {A B X : Pros} (f : ProsHom X A) (g : ProsHom X B)
    : ProsHom X (Pros_prodOb A B).
Proof.
  red. exists (CoqSetoid_fpair f g). pros.
Defined.

Instance Pros_has_products : has_products ProsCat :=
{
    prodOb := Pros_prodOb;
    proj1 := Pros_proj1;
    proj2 := Pros_proj2;
    fpair := @Pros_fpair
}.
Proof.
  proper.
  pros'; setoid'.
Defined.

Definition thin (C : Cat) : Prop :=
    forall (X Y : Ob C) (f g : Hom X Y), f == g.