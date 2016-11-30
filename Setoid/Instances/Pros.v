Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".

Require Import NPeano.
Require Import Omega.

Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprod.

Set Universe Polymorphism.

Class Pros : Type :=
{
    carrier : Type;
    leq : carrier -> carrier -> Prop;
    leq_refl : forall a : carrier, leq a a;
    leq_trans : forall a b c : carrier, leq a b -> leq b c -> leq a c
}.

Coercion carrier : Pros >-> Sortclass.

(*Arguments carr_ _ : clear implicits.*)

Notation "x ≤ y" := (leq x y) (at level 40).

(*Instance SetoidPros : Setoid Pros :=
{
    equiv := fun A B : Pros => JMeq (@leq A) (@leq B)
}.
cat. red. intros. destruct x, y, z; simpl in *. rewrite H, H0. trivial.
Defined.*)

Theorem eq_JMeq : forall (A : Type) (a a' : A), JMeq a a' <-> a = a'.
split; intros. rewrite H. trivial.
rewrite H. trivial.
Qed.

Definition ProsHom (A : Pros) (B : Pros) : Type :=
    {f : A -> B | forall a a', a ≤ a' -> f a ≤ f a'}.

Definition ProsHom_Fun {A B : Pros} (f : ProsHom A B) : A -> B := proj1_sig f.
Coercion ProsHom_Fun : ProsHom >-> Funclass.

Definition ProsComp (A B C : Pros) (f : ProsHom A B) (g : ProsHom B C)
    : ProsHom A C.
Proof.
  destruct f as [f Hf], g as [g Hg]. red.
  exists (fun a : A => g (f a)). intros. apply Hg. apply Hf. auto.
Defined.

Definition ProsId (A : Pros) : ProsHom A A.
Proof.
  red. exists (fun a : A => a). auto.
Defined.

Instance ProsCat : Cat :=
{
    Ob := Pros;
    Hom := ProsHom;
    HomSetoid := fun A B : Pros => {| equiv := fun f g : ProsHom A B =>
        forall x : A, f x = g x |};
    comp := ProsComp;
    id := ProsId
}.
Proof.
  (* Equivalence *) cat. red; intros. rewrite H, H0. auto.
  (* Proper *) repeat red; simpl; intros. unfold ProsComp;
    destruct x, x0, y, y0; simpl in *. rewrite H, H0. auto.
  (* Category laws *) all: unfold ProsComp, ProsId; intros;
  repeat match goal with
      | f : ProsHom ?A ?B |- _ => destruct f
  end; simpl; auto.
Defined.

Instance NatLe : Pros :=
{
    carrier := nat;
    leq := le
}.
Proof. all: intros; omega. Defined.

Definition addOne : ProsHom NatLe NatLe.
Proof.
  red. exists (fun n => S n). simpl; intros; omega.
Defined.

Definition timesTwo : ProsHom NatLe NatLe.
Proof.
  red. exists (fun n => 2 * n). simpl; intros; omega.
Defined.

Definition lst (A : Pros) (a : A) : Prop := forall a' : A, a ≤ a'.

Theorem lst_NatLe : lst NatLe 0.
Proof. unfold lst; simpl; intros; omega. Qed.

Lemma pow_gt_one : forall n : nat, 1 <= 2^n.
Proof. induction n; simpl; omega. Qed.

Definition exp : Hom NatLe NatLe.
Proof.
  red. exists (fun n => 2 ^ n). induction a, a'; simpl; intros; auto.
    apply le_trans with (2 ^ a'). apply pow_gt_one. omega.
    inversion H.
    simpl in *. repeat rewrite plus_0_r. apply le_S_n in H.
      apply NPeano.Nat.add_le_mono. all: apply IHa; auto.
Defined.

(*Theorem Pros_mon_inj : forall (A B : Pros) (f : Hom A B),
    Mon f <-> injective f.
unfold Mon, injective; split; intros.
(* Trivial: use the property that Pros is a contruct over Set. *)
Focus 2.
rewrite fn_ext_pros; intro x. apply H.
generalize x; rewrite fn_ext_pros in H0. assumption.
admit.*)

Instance init' : Pros :=
{
    carrier := Empty_set;
    leq := fun (x y : Empty_set) => match x with end
}.
Proof. all: destruct a. Defined.

Definition create' (X : Pros) : ProsHom init' X.
Proof.
  red. exists (fun (e : init') => match e with end). destruct a.
Defined.

Instance Pros_has_init : has_init ProsCat :=
{
    init := init';
    create := create'
}.
Proof. repeat red. destruct x. Defined.

Instance term' : Pros :=
{
    carrier := unit;
    leq := fun _ _ => True
}.
Proof. all: auto. Defined.

Definition delete' (X : Pros) : ProsHom X term'.
Proof. red. exists (fun _ => tt). simpl. auto. Defined.

Instance Pros_has_term : has_term ProsCat :=
{
    term := term';
    delete := delete'
}.
Proof. simpl; intros; destruct (f x); auto. Defined.

Print term.

Eval compute in term ProsCat.

Definition product_leq {A B : Type} (leqA : A -> A -> Prop)
    (leqB : B -> B -> Prop) (p : A * B) (q : A * B) : Prop := match p, q with
        | (a, b), (a', b') => leqA a a' /\ leqB b b'
    end.

Instance prod'' (X Y : Pros) : Pros :=
{
    carrier := X * Y;
    leq := fun x y : X * Y => leq (fst x) (fst y) /\ leq (snd x) (snd y)
}.
Proof.
  unfold leq; destruct X, Y; simpl. auto.
  unfold leq; destruct X, Y; simpl. destruct 1, 1. split.
    eapply leq_trans0; eauto.
    eapply leq_trans1; eauto.
Defined.

Definition proj1'' (X Y : Pros) : ProsHom (prod'' X Y) X.
Proof. red. exists fst. simpl. destruct 1. auto. Defined.

Definition proj2'' (X Y : Pros) : ProsHom (prod'' X Y) Y.
Proof. red. exists snd. simpl. destruct 1. auto. Defined.

Coercion id (X : Pros) : Ob ProsCat := X.

Program Instance Pros_has_prod : has_products ProsCat :=
{
    prod' := prod''
}.
Next Obligation. exact (proj1'' A B). Defined.
Next Obligation. exact (proj2'' A B). Defined.
Next Obligation.
  repeat red; simpl; intros. unfold ProsHom.
  cut ({f0 : X -> prod'' A B | forall a a' : X, a ≤ a' -> f0 a ≤ f0 a'}).
  Focus 2. exists (fun x : X => (f x, g x)). split; simpl; intros;
    destruct f, g; auto.
    (*intro u. exists u. repeat split; repeat red.
      unfold ProsComp; destruct f, g; try destruct u; simpl; intros.
        destruct A, B, X. simpl in *. eauto. apply leq_antisym.
    intro. destruct (x1 x2)*)