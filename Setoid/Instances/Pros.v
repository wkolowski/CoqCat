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

Notation "x ≤ y" := (leq x y) (at level 40).

Hint Resolve leq_refl leq_trans.

Coercion carrier : Pros >-> Sortclass.

(*Ltac pros_simpl := repeat (red || split); simpl.*)
Ltac pros_simpl := repeat (red || split).

Ltac prosob P := try intros until P;
match type of P with
  | Pros =>
    let a := fresh P "_leq" in
    let b := fresh P "_leq_refl" in
    let c := fresh P "_leq_trans" in destruct P as [P a b c]
  | Ob _ => progress simpl in P; prosob P
end; simpl in *.

Ltac prosobs := repeat
match goal with
  | P : Pros |- _ => prosob P
  | X : Ob _ |- _ => prosob X
end.

(*Theorem eq_JMeq : forall (A : Type) (a a' : A), JMeq a a' <-> a = a'.
Proof.
  split; intros. rewrite H. trivial.
  rewrite H. trivial.
Qed.*)

Definition ProsHom (A B : Pros) : Type :=
    {f : A -> B | forall a a', a ≤ a' -> f a ≤ f a'}.

Definition ProsHom_Fun {A B : Pros} (f : ProsHom A B) : A -> B := proj1_sig f.
Coercion ProsHom_Fun : ProsHom >-> Funclass.

Ltac proshom f := try intros until f;
match type of f with
  | ProsHom _ _ =>
    let a := fresh f "_pres_leq" in destruct f as [f a]
  | Hom _ _ => progress simpl in f; proshom f
end; simpl in *.

Ltac proshoms := repeat
match goal with
  | f : ProsHom _ _ |- _ => proshom f
  | f : Hom _ _ |- _ => proshom f
end.

Ltac pros' := repeat (pros_simpl || prosobs || proshoms || cat || omega).
Ltac pros := try (pros'; fail).

Definition ProsComp (A B C : Pros) (f : ProsHom A B) (g : ProsHom B C)
    : ProsHom A C.
Proof.
  proshoms. exists (fun a : A => g (f a)). pros.
Defined.

Definition ProsId (A : Pros) : ProsHom A A.
Proof.
  pros_simpl. exists (fun a : A => a). pros.
Defined.

Instance ProsCat : Cat :=
{
    Ob := Pros;
    Hom := ProsHom;
    HomSetoid := fun A B : Pros =>
      {| equiv := fun f g : ProsHom A B => forall x : A, f x = g x |};
    comp := ProsComp;
    id := ProsId
}.
Proof.
  (* Equivalence *) pros'. rewrite H, H0. auto.
  (* Proper *) pros'. rewrite H, H0. auto.
  (* Category laws *) all: pros.
Defined.

Instance NatLe : Pros :=
{
    carrier := nat;
    leq := le
}.
Proof. all: pros. Defined.

Definition addOne : ProsHom NatLe NatLe.
Proof.
  red. exists (fun n => S n). pros.
Defined.

Definition timesTwo : ProsHom NatLe NatLe.
Proof.
  red. exists (fun n => 2 * n). pros.
Restart.
  red. exists (fun n => 2 * n).
  induction 1; simpl in *.
    apply le_refl.
    do 2 rewrite <- plus_n_O in *. rewrite (plus_comm m _).
    simpl. do 2 apply le_S. assumption.
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

Definition const (X Y : Pros) (y : Y) : ProsHom X Y.
Proof.
  red. exists (fun _ => y). pros.
Defined.

Theorem Pros_mon_inj : forall (X Y : Pros) (f : ProsHom X Y),
    Mon f <-> injective f.
Proof.
  unfold Mon, injective; split; intros.
    specialize (H NatLe (const _ _ x) (const _ _ y)).
      proshoms. apply H; auto. exact 0.
    simpl. intro. apply H. proshoms. auto.
Defined.

(*Coercion id (X : Pros) : Ob ProsCat := X.*)

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
Abort.


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
Proof.
  red. exists (fun _ => tt). pros.
Defined.

Instance Pros_has_term : has_term ProsCat :=
{
    term := Pros_term;
    delete := Pros_delete
}.
Proof. pros. Defined.

(*Definition Pros_prod_leq {A B : Type} (leqA : A -> A -> Prop)
    (leqB : B -> B -> Prop) (p : A * B) (q : A * B) : Prop := match p, q with
        | (a, b), (a', b') => leqA a a' /\ leqB b b'
    end.*)

Instance Pros_prod (X Y : Pros) : Pros :=
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

Definition Pros_proj1 (X Y : Pros) : ProsHom (Pros_prod X Y) X.
Proof. red. exists fst. destruct 1. auto. Defined.

Definition Pros_proj2 (X Y : Pros) : ProsHom (Pros_prod X Y) Y.
Proof. red. exists snd. destruct 1. auto. Defined.

Definition Pros_diag {X Y Z : Pros} (f : ProsHom X Y) (g : ProsHom X Z)
    : ProsHom X (Pros_prod Y Z).
Proof.
  red. exists (fun x : X => (f x, g x)). pros.
Defined.


Instance Pros_has_prod : has_products ProsCat :=
{
    prod' := Pros_prod;
    proj1' := Pros_proj1;
    proj2' := Pros_proj2
}.
Proof.
  pros_simpl; intros. exists (Pros_diag f g). pros_simpl; intros.
  pros'. rewrite H, H0. destruct (y x). auto.
Defined.

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

(*Definition lex_proj1 (X Y : Pros) : ProsHom (Lexicographic X Y) X.
Proof.
  red. exists fst. destruct a, a', 1; simpl in *; auto.
  destruct H. rewrite H. auto.
Defined.

Definition lex_proj2 (X Y : Pros) : ProsHom (Lexicographic X Y) Y.
Proof.
  red. exists snd. destruct a, a', 1; simpl in *; auto.
  destruct H.
Abort.*)

