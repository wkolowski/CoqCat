Add LoadPath "/home/zeimer/Code/Coq/CoqCat/New".

Require Import NPeano.
Require Import Omega.
Require Import ProofIrrelevance.

Require Export Cat.

Class Pros : Type :=
{
    carrier : Type;
    leq : carrier -> carrier -> Prop;
    leq_refl : forall x : carrier, leq x x;
    leq_trans : forall x y z : carrier, leq x y -> leq y z -> leq x z
}.

Notation "a ≤ b" := (leq a b) (at level 50).

Coercion carrier : Pros >-> Sortclass.

Definition HomPros (A : Pros) (B : Pros) : Type :=
    {f : A -> B | forall x x' : A, leq x x' -> leq (f x) (f x')}.

Definition HomPros_fun {A B : Pros} (f : HomPros A B) : A -> B :=
    proj1_sig f.

Coercion HomPros_fun : HomPros >-> Funclass.

Definition HomProsComp : forall {A B C : Pros} (f : HomPros A B)
    (g : HomPros B C), HomPros A C.
Proof.
  intros. unfold HomPros in *. destruct f as [f Hf], g as [g Hg].
  exists (fun a : A => g (f a)). intros. apply Hg, Hf. auto.
Defined.

Definition HomProsId : forall (A : Pros), HomPros A A.
Proof.
  intros. red. exists (fun x : A => x). intros. auto.
Defined.

Hint Unfold HomPros HomProsComp HomProsId.

Instance CatPros : Cat.
refine
{|
    Ob := Pros;
    Hom := HomPros; (*fun A B : Pros =>
        {f : A -> B | forall x x' : A, leq x x' -> leq (f x) (f x')};*)
    comp := @HomProsComp;
    id := HomProsId
|};
destruct f; try destruct g, h; auto.
Defined.

Instance NatLe : Pros :=
{
  carrier := nat;
  leq := le
}.
Proof. intros. auto. intros. omega. Defined.

Theorem addOne : HomPros NatLe NatLe.
Proof.
  split with (fun n => S n).
  unfold NatLe, leq; intros; omega.
Defined.

Hint Unfold comp Hom HomPros.

(*Coercion id_coer (A B : Pros) (f : @Hom CatPros A B) : HomPros A B := f.*)

Coercion coerr (A B : Pros) (f : @Hom CatPros A B) : HomPros A B := f.

Eval simpl in addOne (addOne 1).

Print Classes.
Print Coercions.

Print Coercion Paths Hom Funclass.
Print Graph.

Coercion c (f : Hom NatLe NatLe) : HomPros NatLe NatLe := f.

Eval simpl in (addOne .> addOne) 1.

Instance timesTwo : HomPros NatLe NatLe.
split with (fun n => 2 * n).
simpl; intros; omega.
Defined.

Axiom fn_ext_pros : forall (A B : Pros') (f : Hom A B) (g : Hom A B),
    f = g <-> forall x : A, f x = g x.

(*Theorem Pros_mon_inj : forall (A B : Pros') (f : Hom A B),
    Mon f <-> injective f.
unfold Mon, injective; split; intros.
(* Trivial: use the property that Pros is a contruct over Set. *)
Focus 2.
rewrite fn_ext_pros; intro x. apply H.
generalize x; rewrite fn_ext_pros in H0. assumption.
admit.*)

Definition product_leq {A B : Type} (leqA : A -> A -> Prop)
    (leqB : B -> B -> Prop) (p : A * B) (q : A * B) : Prop := match p, q with
        | (a, b), (a', b') => leqA a a' /\ leqB b b'
    end.

Definition lst `(A : Pros) (a : A) : Prop := forall a' : A, a ≤ a'.

Theorem lst_NatLe : lst NatLe 0.
unfold lst; simpl; intros; omega.
Qed.

Instance HomProsCat `(A : Pros) : @CatHom A.
split; intros a b. exact (a ≤ b).
Defined.

Instance CompProsCat `(A : Pros) : @CatComp A (HomProsCat A).
split; unfold Hom, HomProsCat; intros.
apply leq_trans with B; assumption.
Defined.

Instance IdProsCat `(A : Pros) : @CatId A (HomProsCat A).
split; unfold Hom, HomProsCat; intros.
apply leq_refl.
Defined.

Instance CatProsCat `(A : Pros) :
    @Cat A (HomProsCat A) (CompProsCat A) (IdProsCat A).
split; unfold Hom, HomProsCat, comp, CompProsCat;
intros; apply proof_irrelevance.
Defined.

(*Instance exp : HomPros NatLe NatLe.
split with (fun n => 2 ^ n).
simpl; intros. induction a, a'; simpl. trivial.
rewrite plus_0_r. SearchPattern (_ ^ _ = _).*)