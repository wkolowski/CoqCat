From Cat Require Import Cat.
From Cat.Universal Require Import
  Initial Terminal Product Coproduct Equalizer Coequalizer IndexedProduct IndexedCoproduct.

Class Apartoid : Type :=
{
  carrier : Type;
  neq : carrier -> carrier -> Prop;
  neq_irrefl  : forall x     : carrier, ~ neq x x;
  neq_sym     :: Symmetric neq; (* forall x y   : carrier, neq x y -> neq y x; *)
  neq_cotrans : forall x y z : carrier, neq x y -> neq z x \/ neq z y
}.

Coercion carrier : Apartoid >-> Sortclass.

Notation "x # y" := (neq x y) (at level 40).

#[global] Hint Resolve neq_irrefl neq_sym neq_cotrans : core.

Ltac apartoidob A := try intros until A;
match type of A with
| Apartoid =>
  let a := fresh A "_neq" in
  let b := fresh A "_neq_irrefl" in
  let c := fresh A "_neq_sym" in
  let d := fresh A "_neq_cotrans" in destruct A as [A a b c d]
| Ob _ => progress cbn in A; apartoidob A
end.

Ltac apartoidobs := intros; repeat
match goal with
| A : Apartoid |- _ => apartoidob A
| X : Ob _ |- _ => apartoidob X
end.

Record ApartoidHom (A B : Apartoid) : Type :=
{
  func :> A -> B;
  reflect_neq : forall a1 a2 : A, func a1 # func a2 -> a1 # a2;
}.

Ltac apartoidhom f := try intros until f;
match type of f with
| ApartoidHom _ _ =>
  let a := fresh "Proper_" f in destruct f as [f a]
| Hom _ _ => progress cbn in f; apartoidhom f
end.

Ltac apartoidhoms := intros; repeat
match goal with
| f : ApartoidHom _ _ |- _ => apartoidhom f
| f : Hom _ _ |- _ => apartoidhom f
end.

Definition ApartoidComp
  (X Y Z : Apartoid) (f : ApartoidHom X Y) (g : ApartoidHom Y Z) : ApartoidHom X Z.
Proof.
  exists (fun x => g (f x)).
  intros a1 a2 Hneq.
  now do 2 apply reflect_neq in Hneq.
Defined.

Definition ApartoidId (X : Apartoid) : ApartoidHom X X.
Proof.
  now exists (fun x : X => x).
Defined.

Ltac apartoid_simpl := repeat (red || split || cbn in * || intros).
Ltac apartoid_simpl' := repeat (apartoid_simpl || apartoidhoms || apartoidobs).

Ltac apartoid_neq := repeat
match goal with
| H : _ \/ _ |- _ => destruct H
| H : ?neq ?x ?x, irrefl : forall x : _, ~ ?neq x x |- False =>
  eapply irrefl; eauto
| H : ?P, H' : ~ ?P |- False =>
  eapply H'; eauto
| H : ?P ?x, H' : forall x : _, ~ ?P x |- False =>
  eapply H'; eauto
| H : ?P (?f _) (?g _), H' : forall x : _, ~ ?P (?f _) (?g _) |- False =>
  try (eapply H'; eauto; fail)
| _ => cat
end.

Ltac apartoid' :=
repeat (apartoid_simpl || apartoid_neq || apartoidobs || apartoidhoms || apartoid_neq;
match goal with
| |- context [Equivalence] => solve_equiv
| |- context [Proper] => proper
| |- False => apartoid_neq
| _ => eauto
end; eauto).
Ltac apartoid := try (apartoid'; eauto; fail).

#[refine]
#[export]
Instance ApartoidCat : Cat :=
{
  Ob := Apartoid;
  Hom := ApartoidHom;
  HomSetoid := fun A B : Apartoid =>
  {|
    equiv := fun f g : ApartoidHom A B => forall a : A, ~ f a # g a
  |};
  comp := ApartoidComp;
  id := ApartoidId
}.
Proof.
  - split; red.
    + now intros; apply neq_irrefl.
    + intros f g Heq a Hneq.
      now apply (Heq a); symmetry.
    + intros f g h Heq1 Heq2 a Hneq.
      destruct (neq_cotrans _ _ (g a) Hneq).
      * now apply (Heq1 a).
      * now apply (Heq2 a).
  - intros A B C f1  f2 Hf g1 g2 Hg a Hneq; cbn in *.
    destruct (neq_cotrans _ _ (g1 (f2 a)) Hneq).
    + apply reflect_neq in H.
      now apply (Hf a); symmetry.
    + now apply (Hg (f2 a)).
  - intros A B C D f g h a Hneq; cbn in *.
    now apply neq_irrefl in Hneq.
  - now cbn; intros; apply neq_irrefl.
  - now cbn; intros; apply neq_irrefl.
Defined.

#[refine]
#[export]
Instance Apartoid_init : Apartoid :=
{
  carrier := Empty_set;
  neq := fun (e : Empty_set) _ => match e with end
}.
Proof. all: easy. Defined.

Definition Apartoid_create (X : Apartoid) : ApartoidHom Apartoid_init X :=
{|
  func := fun e : Apartoid_init => match e with end;
  reflect_neq := ltac:(easy);
|}.

#[refine]
#[export]
Instance HasInit_Apartoid : HasInit ApartoidCat :=
{
  init := Apartoid_init;
  create := Apartoid_create
}.
Proof. easy. Defined.

#[export]
Instance HasStrictInit_Apartoid : HasStrictInit ApartoidCat.
Proof.
  intros A f.
  exists (create A).
  split; cycle 1.
  - now apply equiv_initial.
  - destruct f as [f Hf]; cbn.
    now intros x; destruct (f x).
Defined.

#[refine]
#[export]
Instance Apartoid_term : Apartoid :=
{
  carrier := unit;
  neq := fun _ _ => False
}.
Proof. all: easy. Defined.

Definition Apartoid_delete (X : Apartoid) : ApartoidHom X Apartoid_term.
Proof.
  now exists (fun _ => tt).
Defined.

#[refine]
#[export]
Instance HasTerm_Apartoid : HasTerm ApartoidCat :=
{
  term := Apartoid_term;
  delete := Apartoid_delete
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance Apartoid_product (X Y : Apartoid) : Apartoid :=
{
  carrier := X * Y;
  neq := fun (p1 : X * Y) (p2 : X * Y) =>
    neq (fst p1) (fst p2) \/ neq (snd p1) (snd p2)
}.
Proof.
  - now intros [x y]; cbn; apartoid.
  - now intros [x1 y1] [x2 y2]; cbn; apartoid.
  - intros [x1 y1] [x2 y2] [x3 y3] []; cbn in *.
    + now destruct (neq_cotrans _ _ x3 H); auto.
    + now destruct (neq_cotrans _ _ y3 H); auto.
Defined.

Definition Apartoid_outl (X Y : Apartoid) : ApartoidHom (Apartoid_product X Y) X.
Proof.
  exists fst.
  now cbn; left.
Defined.

Definition Apartoid_outr (X Y : Apartoid) : ApartoidHom (Apartoid_product X Y) Y.
Proof.
  exists snd.
  now cbn; right.
Defined.

Definition Apartoid_fpair
  (A B X : Apartoid) (f : ApartoidHom X A) (g : ApartoidHom X B)
  : ApartoidHom X (Apartoid_product A B).
Proof.
  exists (fun x : X => (f x, g x)).
  now cbn; intros a1 a2 [H%reflect_neq | H%reflect_neq].
Defined.

#[refine]
#[export]
Instance HasProducts_Apartoid : HasProducts ApartoidCat :=
{
  product := Apartoid_product;
  outl := Apartoid_outl;
  outr := Apartoid_outr;
  fpair := Apartoid_fpair
}.
Proof.
  split; cbn.
  - easy.
  - easy.
  - now firstorder.
Defined.

#[refine]
#[export]
Instance Apartoid_coproduct (X Y : Apartoid) : Apartoid :=
{
    carrier := X + Y;
    neq := fun p1 p2 : X + Y =>
      match p1, p2 with
      | inl x, inl x' => neq x x'
      | inr y, inr y' => neq y y'
      | _, _ => True
      end
}.
Proof.
  - now intros [x | y].
  - now intros [x1 | y1] [x2 | y2]; auto.
  - now intros [x1 | y1] [x2 | y2] [x3 | y3]; auto.
Defined.

Definition Apartoid_finl
  (X Y : Apartoid) : ApartoidHom X (Apartoid_coproduct X Y).
Proof.
  now exists inl.
Defined.

Definition Apartoid_finr
  (X Y : Apartoid) : ApartoidHom Y (Apartoid_coproduct X Y).
Proof.
  now exists inr.
Defined.

Definition Apartoid_copair
  (A B X : Apartoid) (f : ApartoidHom A X) (g : ApartoidHom B X)
  : ApartoidHom (Apartoid_coproduct A B) X.
Proof.
  exists (fun p : A + B =>
    match p with
    | inl a => f a
    | inr b => g b
    end).
  now intros [a1 | b1] [a2 | b2]; apartoid.
Defined.

#[refine]
#[export]
Instance HasCoproducts_Apartoid : HasCoproducts ApartoidCat :=
{
  coproduct := Apartoid_coproduct;
  finl := Apartoid_finl;
  finr := Apartoid_finr;
  copair := Apartoid_copair
}.
Proof.
  split; cbn; [easy | easy |].
  intros P' [h1 h1'] [h2 h2'] Heq1 Heq2 [a | b] H; cbn in H, Heq1, Heq2.
  - now apply (Heq1 a).
  - now apply (Heq2 b).
Defined.

#[refine]
#[export]
Instance Apartoid_indexedProduct {J : Type} (A : J -> Apartoid) : Apartoid :=
{
  carrier := forall j : J, A j;
  neq := fun f g : forall j : J, A j => exists j : J, f j # g j
}.
Proof.
  - now intros x [j H]; apply neq_irrefl with (x j).
  - intros x y [j H].
    exists j.
    now apply neq_sym.
  - intros x y z [j H].
    destruct (neq_cotrans (x j) (y j) (z j) H).
    + now left; exists j.
    + now right; exists j.
Defined.

Definition Apartoid_out
  {J : Type} (A : J -> Apartoid) (j : J) : ApartoidHom (Apartoid_indexedProduct A) (A j).
Proof.
  exists (fun (f : forall j : J, A j) => f j).
  cbn; intros a1 a2 Hneq.
  now exists j.
Defined.

Definition Apartoid_tuple
  {J : Type} {A : J -> Apartoid} {X : Apartoid}
  (f : forall j : J, ApartoidHom X (A j))
  : ApartoidHom X (Apartoid_indexedProduct A).
Proof.
  exists (fun (x : X) (j : J) => f j x).
  cbn; intros a1 a2 [j Hneq].
  now apply reflect_neq in Hneq.
Defined.

#[refine]
#[export]
Instance HasIndexedProducts_Apartoid : HasIndexedProducts ApartoidCat :=
{
  indexedProduct := @Apartoid_indexedProduct;
  out := @Apartoid_out;
  tuple := @Apartoid_tuple;
}.
Proof.
  split; cbn in *; intros.
  - easy.
  - intros [j Hj].
    now apply (H j a).
Defined.

#[refine]
#[export]
Instance Apartoid_equalizer {X Y : Apartoid} (f g : ApartoidHom X Y) : Apartoid :=
{
  carrier := {x : X | ~ (f x) # (g x)};
  neq := fun p1 p2 : {x : X | ~ (f x) # (g x)} =>
    proj1_sig p1 # proj1_sig p2
}.
Proof.
  - easy.
  - easy.
  - intros [x Hx] [y Hy] [z Hz]; cbn.
    now apply neq_cotrans.
Defined.

Definition Apartoid_equalize
  {X Y : Apartoid} (f g : ApartoidHom X Y) : ApartoidHom (Apartoid_equalizer f g) X.
Proof.
  exists (@proj1_sig _ _).
  now cbn.
Defined.

Lemma trick
  (X Y E' : Apartoid) (f g : Hom X Y)
  (e' : Hom E' X) (H : e' .> f == e' .> g)
  : E' -> Apartoid_equalizer f g.
Proof.
  intros x; cbn in *.
  now exists (e' x).
Defined.

Lemma Apartoid_factorize
  (X Y : Apartoid) (f g : Hom X Y)
  (E' : Apartoid) (e' : Hom E' X) (H : e' .> f == e' .> g)
  : ApartoidHom E' (Apartoid_equalizer f g).
Proof.
  exists (trick X Y E' f g e' H); cbn.
  now intros a1 a2 Hneq%reflect_neq.
Defined.

#[refine]
#[export]
Instance HasEqualizers_Apartoid : HasEqualizers ApartoidCat :=
{
  equalizer := @Apartoid_equalizer;
  equalize := @Apartoid_equalize;
  factorize := @Apartoid_factorize;
}.
Proof.
  intros A B f g; split; cbn.
  - now intros [a Ha]; cbn.
  - now intros E' e' Hneq x.
  - easy.
Defined.

Inductive ACN {A B : Apartoid} (f g : ApartoidHom A B) : B -> B -> Prop :=
| ACN_glue :
  forall b1 b2 : B, b1 # b2 ->
  (forall a1 a2 : A, b1 = f a1 /\ b2 = g a2 -> False) ->
    ACN f g b1 b2
| ACN_sym : forall b1 b2 : B, ACN f g b1 b2 -> ACN f g b2 b1.

#[refine]
#[export]
Instance Apartoid_coequalizer {A B : Apartoid} (f g : ApartoidHom A B) : Apartoid :=
{
  carrier := B;
  neq := ACN f g;
}.
Proof.
  - intros x1.
    pose (x2 := x1); assert (Heq : x1 = x2) by easy.
    change (~ ACN f g x1 x2); clearbody x2.
    induction 1; subst.
    + now apply neq_irrefl in H.
    + now apply IHACN.
  - now red; apply ACN_sym.
  - induction 1.
    + destruct (neq_cotrans _ _ z H).
      * left; constructor; [easy |].
Abort.

#[refine]
#[export]
Instance Apartoid_indexedCoproduct {J : Apartoid} (A : J -> Apartoid) : Apartoid :=
{
  carrier := {j : J & A j};
  neq := fun p1 p2 : {j : J & A j} => projT1 p1 # projT1 p2
}.
Proof.
  - now intros [x x']; auto.
  - now intros [x x'] [y y']; cbn; auto.
  - now intros [x x'] [y y'] [z z']; cbn; auto.
Defined.

Definition Apartoid_inj
  {J : Apartoid} (A : J -> Apartoid) (j : J) : ApartoidHom (A j) (Apartoid_indexedCoproduct A).
Proof.
  exists (fun a : A j => existT _ j a); cbn.
  intros a1 a2 Hneq.
  now apply neq_irrefl in Hneq.
Defined.

Definition Apartoid_indexedCopair
  {J : Apartoid} {A : J -> Apartoid}
  {X : Apartoid} (f : forall j : J, ApartoidHom (A j) X)
  : ApartoidHom (Apartoid_indexedCoproduct A) X.
Proof.
  exists (fun p : {j : J & A j} => f (projT1 p) (projT2 p)).
Abort.