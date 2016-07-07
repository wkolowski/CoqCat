Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".

Require Import NPeano.
Require Import Omega.

Require Export Cat.

(*Class Pros {A : Type} : Type :=
{
    leq : A -> A -> Prop;
    leq_refl : forall a : A, leq a a;
    leq_trans : forall a b c : A, leq a b -> leq b c -> leq a c
}.*)

Class Pros : Type :=
{
    carr_ : Type;
    leq : carr_ -> carr_ -> Prop;
    leq_refl : forall a : carr_, leq a a;
    leq_trans : forall a b c : carr_, leq a b -> leq b c -> leq a c
}.

Notation "a ≤ b" := (leq a b) (at level 50).

Definition Pros_Sort (A : Pros) := @carr_ A.
Coercion Pros_Sort : Pros >-> Sortclass.

(*Class HomPros `(A : Pros) `(B : Pros) : Type :=
{
    f_ : A -> B;
    homo_pros : forall a a' : A, a ≤ a' -> f_ a ≤ f_ a'
}.*)

Definition HomPros (A : Pros) (B : Pros) : Type :=
    {f : A -> B | forall a a', a ≤ a' -> f a ≤ f a'}.

Definition HomPros_Fun (A B : Pros) (f : HomPros A B) := proj1_sig f.
Coercion HomPros_Fun : HomPros >-> Funclass.



(*Class HomPros (A B : Pros) : Type :=
{
    f_ : A -> B;
    homo : forall a a' : A, a ≤ a' -> f_ a ≤ f_ a'
}.

Definition HomPros_Fun (A B : Pros) (f : HomPros A B) := @f_ A B f.
Coercion HomPros_Fun : HomPros >-> Funclass.*)

(*Theorem add2 : forall (A : Pros) (f : HomPros A A) (a : A), a = f a.
trivial.
Qed.*)

(*Class Pros' : Type :=
{
    carrier_ : Type;
    pros_ : @Pros carrier_
}.*)

(*Definition Pros'_Pros `(_ : Pros') := pros_.
Coercion Pros'_Pros : Pros' >-> Pros.
*)
Print Pros_Sort.
Instance CatPros : Cat :=
{
    Ob := Pros;
    Hom := HomPros;
    Hom_Setoid := fun A B : Pros => {| equiv := fun f g : HomPros A B =>
        forall x : A, f x = g x |};
    (*comp := fun (A B C : Pros) (f : Hom A B) (g : Hom B C) => f .> g*)
}.
split; auto; unfold Transitive; intros; rewrite H, H0; trivial.
intros. destruct X as [f f_homo], X0 as [g g_homo].
exists (fun a : A => g (f a)). intros. apply g_homo, f_homo. trivial.
unfold Proper, respectful; intros. destruct x, y, x0, y0; simpl in *.
intro. rewrite H, H0. trivial.
intro. unfold HomPros. exists (fun a : A => a). trivial.
destruct f, g, h; cat2.
destruct f; cat2. destruct f; cat2.
Defined.

Instance NatLe : @Pros nat.
split with le; intros; omega.
Defined.

Instance addOne : HomPros NatLe NatLe.
split with (fun n => S n).
unfold NatLe, leq; intros; omega.
Defined.

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