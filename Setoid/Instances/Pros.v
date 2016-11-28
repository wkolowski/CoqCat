Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".

Require Import NPeano.
Require Import Omega.

Require Export Cat.

Class Pros : Type :=
{
    carr_ : Type;
    leq : carr_ -> carr_ -> Prop;
    leq_refl : forall a : carr_, leq a a;
    leq_trans : forall a b c : carr_, leq a b -> leq b c -> leq a c
}.

Arguments carr_ _ : clear implicits.

Instance SetoidPros : Setoid Pros :=
{
    equiv := fun A B : Pros => JMeq (@leq A) (@leq B)
}.
split.
unfold Reflexive. trivial.
unfold Symmetric. intros. rewrite H. trivial.
unfold Transitive. intros. rewrite H, H0. trivial.
Defined.

Print SetoidPros.

Theorem eq_JMeq : forall (A : Type) (a a' : A), JMeq a a' <-> a = a'.
split; intros. rewrite H. trivial.
rewrite H. trivial.
Qed.

Notation "a ≤ b" := (leq a b) (at level 50).

Definition Pros_Sort (A : Pros) := @carr_ A.
Coercion Pros_Sort : Pros >-> Sortclass.

Definition HomPros (A : Pros) (B : Pros) : Type :=
    {f : A -> B | forall a a', a ≤ a' -> f a ≤ f a'}.

Definition HomPros_Fun (A B : Pros) (f : HomPros A B) := proj1_sig f.
Coercion HomPros_Fun : HomPros >-> Funclass.

Print Pros_Sort.
Instance CatPros : Cat :=
{
    Ob := Pros;
    Hom := HomPros;
    HomSetoid := fun A B : Pros => {| equiv := fun f g : HomPros A B =>
        forall x : A, f x = g x |};
}.
split; auto; unfold Transitive; intros; rewrite H, H0; trivial.
intros. destruct X as [f f_homo], X0 as [g g_homo].
exists (fun a : A => g (f a)). intros. apply g_homo, f_homo. trivial.
unfold Proper, respectful; intros. destruct x, y, x0, y0; simpl in *.
intro. rewrite H, H0. trivial.
destruct f, g, h. simpl. cat2.
intro. unfold HomPros. exists (fun a : A => a). trivial.
destruct f; cat2. destruct f; cat2.
Defined.

Class Pros {A : Type} : Type :=
{
    leq : A -> A -> Prop;
    leq_refl : forall a : A, leq a a;
    leq_trans : forall a b c : A, leq a b -> leq b c -> leq a c
}.
Print Setoid.
Instance SetoidPros (A : Type) : Setoid (@Pros A).
refine {| equiv := fun P Q : @Pros A => @leq A P = @leq A Q |}.
split.
unfold Reflexive. trivial.
unfold Symmetric; intros. rewrite H. reflexivity.
unfold Transitive; intros; rewrite H, H0; reflexivity.
Defined.

Class Pros' : Type :=
{
    carr_ :> Type;
    pros_ :> @Pros carr_;
    setoid_ : 
}.


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