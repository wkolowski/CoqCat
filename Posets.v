Require Omega.
Require Import ZArith.
Require Import NPeano.

Class Preord {A : Type} (leq : A -> A -> Prop) : Type :=
{
    refl : forall a : A, leq a a;
    trans : forall a b c : A, leq a b -> leq b c -> leq a c
}.

Class Poset (A : Type) (leq : A -> A -> Prop) : Type :=
{
    proset : Preord leq;
    wasym : forall a b : A, leq a b -> leq b a -> a = b
}.

(*Lemma l1 : forall n : nat, n <= 0 -> n = 0.
induction n as [| n'].
Case "1". trivial.
Case "IH". intro. inversion H.
Qed.

Lemma l2 : forall n m : nat, S n = S m -> n = m.
induction n, m. trivial. intros. inversion H.
intros. inversion H.
intros. inversion H. trivial.
Qed.

Lemma l3 : forall n m : nat, n = m -> S n = S m.
induction n, m; auto.
Qed.

Lemma l4 : forall n m : nat, n <= m -> S n <= S m.
induction m; generalize dependent n. intros. inversion H. apply le_n.
intros. inversion H. apply le_n. apply le_S. apply IHm. assumption.
Qed.*)

(*Lemma l5 : forall n m : nat, S n <= S m -> n <= m.
induction m as [| m']; generalize dependent n. intros.
inversion H. apply le_n. inversion H2.
induction n as [| n']; intros.
apply le_0_l.
induction H.
 apply l4.
inversion H. apply le_n.*)

Instance NatLe : Poset nat le.
split; [split; intros; omega | intros; omega].
Defined.

(*Case "refl". intro; apply le_n.
Case "trans". induction a as [| a']; induction b as [| b'].
    SCase "a = 0, b = 0". trivial.
    SCase "a = 0, b = S b'". intros; apply le_0_l.
    SCase "a = S a', b = 0". intros. inversion H.
    SCase "a = S a', b = S b'". intros. inversion H. assumption.
        apply IHb'. apply H3. apply Sn_le_n_le. assumption.
Case "wasym". induction a as [| a']; induction b as [| b'].
    SCase "a = 0, b = 0". trivial.
    SCase "a = 0, b = S b'". intros; inversion H0.
    SCase "a = S a', b = 0". intros; inversion H.
    SCase "a = S a', b = S b'". intros. apply f_equal.
        inversion H. trivial. inversion H0. trivial. apply IHa'.
        SSCase "IH 1". apply Sn_le_n_le in H3. assumption.
        SSCase "IH 2". apply Sn_le_n_le in H6. assumption.
Qed.*)

Class HomPos2 {A B : Type} {leqA : A -> A -> Prop} {leqB : B -> B -> Prop}
    (f : A -> B) : Type :=
{
    dom :> Poset A leqA;
    cod : Poset B leqB;
    hom : forall a a' : A, leqA a a' -> leqB (f a) (f a') 
}.

Instance addOne2 : @HomPos2 nat nat le le (fun n : nat => n + 1).
split. apply NatLe. apply NatLe.
intros. omega.
Defined.

Definition HomPos {A B : Type} {leqA : A -> A -> Prop}
{leqB : B -> B -> Prop} (p1 : Poset A leqA) (p2 : Poset B leqB) : Type :=
    {f : A -> B | forall x y : A, leqA x y -> leqB (f x) (f y)}.

Notation "'Sig_no'"  := (False_rec _ _) (at level 42).
Notation "'Sig_yes' e" := (exist _ e _) (at level 42).
Notation "'Sig_take' e" := 
  (match e with Sig_yes ex => ex end) (at level 42). 

Definition f : forall n : nat, {m : nat | m = S n}.
    refine (fun n => Sig_yes (S n)). trivial.
Defined.

(*Definition g : HomPos NatLe NatLe.
    refine (exist (fun f => forall x y : nat, x <= y -> (f x) <= (f y))
          (fun n => S n) _).*)

Definition g : HomPos NatLe NatLe.
    refine (Sig_yes (fun n => S n)). intros; omega.
(*intros. apply l4. assumption.*)
Defined.

(*Lemma l6 : forall x y : nat, S x <= S y -> x <= S y.
induction x as [| x'], y as [| y']; intros.
apply le_0_l.
apply le_0_l.
inversion H. inversion H2.
apply l4. apply IHx'. *)

(* Alternative development. *)
(*Inductive Poset :=
    | Pos : (A : Type) (leq : A -> a -> Prop) (
*)

Record Pos : Type := Pos2
{
    U : Type;
    leq : U -> U -> Prop;
    refl' : forall a : U, leq a a;
    wasym' : forall a b : U, leq a b -> leq b a -> a = b;
    trans' : forall a b c : U, leq a b -> leq b c -> leq a c
}.

Variable A : Pos.

Class HomPos' {A B : Type} {leqA : A -> A -> Prop} {leqB : B -> B -> Prop}
(PA : Poset A leqA) (PB : Poset B leqB) (f : A -> B) : Prop := mkHomPos
{
    homo' : forall a a' : A, leqA a a' -> leqB (f a) (f a')
}.

Definition addOne (n : nat) := n + 1.

Instance addOne' : HomPos' NatLe NatLe addOne.
split. intros. unfold addOne. induction a as [| b], a' as [| b'].
simpl. apply le_n. simpl. omega.

Record HomPos22 (A : Pos) (B : Pos) : Type := HomPos3
{
    f' : U A -> U B;
    homo : forall a a' : U A, leq A a a' -> leq B (f' a) (f' a')
}.





Lemma l7 : forall a b c d, a <= c -> b <= d -> (a + b) <= (c + d).
intros. induction H. rewrite plus_comm.

Definition h : HomPos NatLe NatLe.
refine (Sig_yes (fun n => 2 * n)). intros; omega.
(*intros. induction x, y; auto. apply le_0_l. inversion H.
rewrite mult_n_Sm. assert (2 * x <= 2 * S y).
apply IHx. 


rewrite plus_n_0. rewrite plus_n_0. apply l4.
rewrite <- plus_n_Sm, <- plus_n_Sm. apply l4. simpl in IHx.
rewrite plus_n_0 in IHx. rewrite plus_n_0 in IHx.
rewrite plus_n_Sm in IHx. inversion H. apply le_n.*)