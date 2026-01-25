From Cat Require Export Cat.
From Cat.Universal Require Export Initial Terminal Product Coproduct.
From Cat Require Export Instances.SETOID.

Set Implicit Arguments.

Class Pros : Type :=
{
  carrier :: Setoid';
  leq : carrier -> carrier -> Prop;
  Proper_leq :: Proper (equiv ==> equiv ==> equiv) leq;
  leq_refl : forall a b : carrier, a == b -> leq a b;
  leq_trans : forall a b c : carrier, leq a b -> leq b c -> leq a c
}.

Notation "x ≤ y" := (leq x y) (at level 40).

#[global] Hint Resolve leq_refl leq_trans : core.

Coercion carrier : Pros >-> Setoid'.

Ltac pros_simpl := repeat (cbn in * || red || split).

Ltac prosob P := try intros until P;
match type of P with
| Pros =>
  let a := fresh P "_leq" in
  let b := fresh P "_leq_refl" in
  let c := fresh P "_leq_trans" in destruct P as [P a b c]
| Ob _ => progress cbn in P; prosob P
end; cbn in *.

Ltac prosob' P := prosob P; setoidob P.

Ltac prosobs_template tac := intros; repeat
match goal with
| P : Pros |- _ => tac P
| X : Ob _ |- _ => tac X
end.

Ltac prosobs := prosobs_template prosob.
Ltac prosobs' := prosobs_template prosob'.

Definition ProsHom (A B : Pros) : Type :=
  {f : SetoidHom A B| forall a a', a ≤ a' -> f a ≤ f a'}.

Definition ProsHom_Fun {A B : Pros} (f : ProsHom A B) : SetoidHom A B := proj1_sig f.
Coercion ProsHom_Fun : ProsHom >-> SetoidHom.

Ltac proshom f := try intros until f;
match type of f with
| ProsHom _ _ =>
  let a := fresh f "_pres_leq" in destruct f as [f a]
| Hom _ _ => progress cbn in f; proshom f
end; cbn in *.

Ltac proshom' f := proshom f; setoidhom f.

Ltac proshoms_template tac := intros; repeat
match goal with
| f : ProsHom _ _ |- _ => tac f
| f : Hom _ _ |- _ => tac f
end.

Ltac proshoms := proshoms_template proshom.
Ltac proshoms' := proshoms_template proshom'.

Ltac pros' := repeat (pros_simpl || proshoms || prosobs || setoid' || lia).
Ltac pros := try (pros'; fail).

Definition ProsComp (A B C : Pros) (f : ProsHom A B) (g : ProsHom B C) : ProsHom A C.
Proof.
  exists (SetoidComp f g).
  now pros.
Defined.

Definition ProsId (A : Pros) : ProsHom A A.
Proof.
  now exists (@SetoidId A).
Defined.

#[refine]
#[export]
Instance ProsCat : Cat :=
{
  Ob := Pros;
  Hom := ProsHom;
  HomSetoid := fun A B : Pros =>
  {|
    equiv := fun f g : ProsHom A B => forall x : A, @equiv _ B (f x) (g x)
  |};
  comp := ProsComp;
  id := ProsId
}.
Proof.
  - now solve_equiv.
  - intros A B C f1 f2 Hf g1 g2 Hg x; cbn in *.
    now rewrite Hf, Hg.
  - now cbn.
  - now cbn.
  - now cbn.
Defined.

Lemma Pros_isMono_inj :
  forall (X Y : Pros) (f : ProsHom X Y),
    isMono f <-> injectiveS f.
Proof.
Abort.

Lemma Pros_isEpi_sur :
  forall (X Y : Pros) (f : ProsHom X Y),
    isEpi f <-> surjective f.
Proof.
Abort.

Lemma Pros_isSec_inj :
  forall (X Y : Pros) (f : ProsHom X Y),
    isSec f <-> injectiveS f.
Proof.
Abort.

#[refine]
#[export]
Instance Pros_init : Pros :=
{
  carrier := SETOID_init;
  leq := fun (x y : Empty_set) => match x with end
}.
Proof. all: easy. Defined.

Definition Pros_create (X : Pros) : ProsHom Pros_init X.
Proof.
  now exists (SETOID_create X).
Defined.

#[refine]
#[export]
Instance HasInit_Pros : HasInit ProsCat :=
{
  init := Pros_init;
  create := Pros_create
}.
Proof. easy. Defined.

#[export]
Instance HasStrictInit_Pros : HasStrictInit ProsCat.
Proof.
  intros A [f Hf]; cbn in f.
  exists (create A); split.
  - now intros x; destruct (f x).
  - now apply equiv_initial.
Defined.

#[refine]
#[export]
Instance Pros_term : Pros :=
{
  carrier := SETOID_term;
  leq := fun _ _ => True
}.
Proof. all: easy. Defined.

Definition Pros_delete (X : Pros) : ProsHom X Pros_term.
Proof.
  now exists (SETOID_delete X).
Defined.

#[refine]
#[export]
Instance HasTerm_Pros : HasTerm ProsCat :=
{
  term := Pros_term;
  delete := Pros_delete
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance Pros_product (X Y : Pros) : Pros :=
{
  carrier := SETOID_product X Y;
  leq := fun x y : X * Y => leq (fst x) (fst y) /\ leq (snd x) (snd y)
}.
Proof.
  - intros f1 f2 [Hf1 Hf2] g1 g2 [Hg1 Hg2]; cbn in *.
    now rewrite Hf1, Hf2, Hg1, Hg2.
  - now pros.
  - now pros.
Defined.

Definition Pros_outl (X Y : Pros) : ProsHom (Pros_product X Y) X.
Proof.
  now exists (SETOID_outl X Y); cbn.
Defined.

Definition Pros_outr (X Y : Pros) : ProsHom (Pros_product X Y) Y.
Proof.
  now exists (SETOID_outr X Y); cbn.
Defined.

Definition Pros_fpair
  {A B X : Pros} (f : ProsHom X A) (g : ProsHom X B) : ProsHom X (Pros_product A B).
Proof.
  exists (SETOID_fpair f g).
  now pros.
Defined.

#[refine]
#[export]
Instance HasProducts_Pros : HasProducts ProsCat :=
{
  product := Pros_product;
  outl := Pros_outl;
  outr := Pros_outr;
  fpair := @Pros_fpair
}.
Proof.
  now repeat split; cbn in *.
Defined.

(* Definition thin (C : Cat) : Prop :=
  forall (X Y : Ob C) (f g : Hom X Y), f == g. *)

#[refine]
#[export]
Instance Pros_coproduct (X Y : Pros) : Pros :=
{
  carrier := SETOID_coproduct X Y;
  leq := fun a b : X + Y =>
    match a, b with
    | inl x, inl x' => x ≤ x'
    | inr y, inr y' => y ≤ y'
    | _, _ => False
    end
}.
Proof.
  - now intros [x1 | y1] [x2 | y2] H12 [x3 | y3] [x4 | y4] H34; cbn in *;
      rewrite ?H12, ?H34; eauto.
  - now intros [x1 | y1] [x2 | y2] Heq; cbn in *; eauto.
  - now intros [x1 | y1] [x2 | y2] [x3 | y3] H12 H23; cbn in *; eauto.
Defined.

Definition Pros_finl (X Y : Pros) : ProsHom X (Pros_coproduct X Y).
Proof.
  now exists (SETOID_finl X Y).
Defined.

Definition Pros_finr (X Y : Pros) : ProsHom Y (Pros_coproduct X Y).
Proof.
  now exists (SETOID_finr X Y).
Defined.

Definition Pros_copair
  (A B X : Pros) (f : ProsHom A X) (g : ProsHom B X) : ProsHom (Pros_coproduct A B) X.
Proof.
  exists (SETOID_copair f g).
  now intros [] []; pros.
Defined.

#[refine]
#[export]
Instance HasCoproducts_Pros : HasCoproducts ProsCat :=
{
  coproduct := Pros_coproduct;
  finl := Pros_finl;
  finr := Pros_finr;
  copair := Pros_copair
}.
Proof.
  split; cbn.
  - easy.
  - easy.
  - now intros P' h1 h2 HA HB [a | b].
Defined.
