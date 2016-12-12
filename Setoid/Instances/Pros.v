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

Hint Resolve leq_refl leq_trans.

Coercion carrier : Pros >-> Sortclass.

Ltac destr_pros :=
match goal with
  | P : Pros |- _ => destruct P; destr_pros
  | _ => idtac
end; simpl in *.

Notation "x ≤ y" := (leq x y) (at level 40).

Theorem eq_JMeq : forall (A : Type) (a a' : A), JMeq a a' <-> a = a'.
Proof.
  split; intros. rewrite H. trivial.
  rewrite H. trivial.
Qed.

Definition ProsHom (A B : Pros) : Type :=
    {f : A -> B | forall a a', a ≤ a' -> f a ≤ f a'}.

Definition ProsHom_Fun {A B : Pros} (f : ProsHom A B) : A -> B := proj1_sig f.
Coercion ProsHom_Fun : ProsHom >-> Funclass.

Ltac destr_proshom :=
match goal with
  | f : ProsHom _ _ |- _ => destruct f; destr_proshom
  | f : Hom _ _ |- _ => destruct f; destr_proshom
  | _ => idtac
end; simpl in *.

Ltac pros := cat.

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
  (* Equivalence *) cat; red; intros. rewrite H, H0. auto.
  (* Proper *) repeat red; simpl; intros. destr_proshom.
    rewrite H, H0. auto.
  (* Category laws *) all: intros; destr_proshom; pros.
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

Instance NatDiv : Pros :=
{
    carrier := nat;
    leq := fun n m : nat => exists k : nat, n * k = m
}.
Proof.
  exists 1. omega.
  destruct 1 as [k1 H1], 1 as [k2 H2].
    exists (k1 * k2). rewrite mult_assoc. rewrite H1, H2. trivial.
Defined.

(*Theorem Pros_mon_inj : forall (A B : Pros) (f : Hom A B),
    Mon f <-> injective f.
unfold Mon, injective; split; intros.
(* Trivial: use the property that Pros is a contruct over Set. *)
Focus 2.
rewrite fn_ext_pros; intro x. apply H.
generalize x; rewrite fn_ext_pros in H0. assumption.
admit.*)

Instance Pros_init : Pros :=
{
    carrier := Empty_set;
    leq := fun (x y : Empty_set) => match x with end
}.
Proof. all: destruct a. Defined.

Definition Pros_create (X : Pros) : ProsHom Pros_init X.
Proof.
  red. exists (fun (e : Pros_init) => match e with end). destruct a.
Defined.

Instance Pros_has_init : has_init ProsCat :=
{
    init := Pros_init;
    create := Pros_create
}.
Proof. pros. Defined.

Instance Pros_term : Pros :=
{
    carrier := unit;
    leq := fun _ _ => True
}.
Proof. all: auto. Defined.

Definition Pros_delete (X : Pros) : ProsHom X Pros_term.
Proof. red. exists (fun _ => tt). simpl. auto. Defined.

Instance Pros_has_term : has_term ProsCat :=
{
    term := Pros_term;
    delete := Pros_delete
}.
Proof. pros. Defined.

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
Restart.
  all: pros.
Defined.

Definition proj1'' (X Y : Pros) : ProsHom (prod'' X Y) X.
Proof. red. exists fst. simpl. destruct 1. auto. Defined.

Definition proj2'' (X Y : Pros) : ProsHom (prod'' X Y) Y.
Proof. red. exists snd. simpl. destruct 1. auto. Defined.

Coercion id (X : Pros) : Ob ProsCat := X.

Instance Lexicographic (X Y : Pros) : Pros :=
{
    carrier := X * Y;
    leq := fun x y : X * Y => leq (fst x) (fst y) \/
        ((fst x = fst y) /\ leq (snd x) (snd y))
}.
Proof.
  left. apply leq_refl.
  intros. destruct H, H0; try destruct H; try destruct H0.
    left. eauto.
    left. rewrite <- H0. auto.
    left. rewrite H. auto.
    right. split; try rewrite H; eauto.
Defined.

Definition lex_proj1 (X Y : Pros) : ProsHom (Lexicographic X Y) X.
Proof.
  red. exists fst. destruct a, a', 1; simpl in *; auto.
  destruct H. rewrite H. auto.
Defined.

Definition lex_proj2 (X Y : Pros) : ProsHom (Lexicographic X Y) Y.
Proof.
  red. exists snd. destruct a, a', 1; simpl in *; auto.
Abort.

Instance Pros_has_prod : has_products ProsCat :=
{
    prod' := prod'';
    proj1' := proj1'';
    proj2' := proj2''
}.
Proof.
  repeat red; simpl; intros. unfold ProsHom.
  assert (h' : {h : X -> prod'' A B |
                (forall x x' : X, x ≤ x' -> h x ≤ h x') &
                (forall x : X, f x = fst (h x)) /\
                (forall x : X, g x = snd (h x))}).
    exists (fun x : X => (f x, g x)); destruct f, g; simpl in *;
      split; auto.
  destruct h' as [h H [eq1 eq2]]. exists (exist _ h H).
  repeat (red || split || simpl); intros; auto.
  destruct y as [h' H']; simpl in *. destruct H0.
  rewrite surjective_pairing at 1; rewrite surjective_pairing. f_equal.
    rewrite <- H0, eq1. auto.
    rewrite <- H1, eq2. auto.
Defined.