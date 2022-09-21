From Cat Require Import Cat.
From Cat.Universal Require Import
  Initial Terminal Product Coproduct Equalizer Coequalizer IndexedProduct IndexedCoproduct.

Class Apartoid : Type :=
{
  carrier : Type;
  neq : carrier -> carrier -> Prop;
  neq_irrefl : forall x : carrier, ~ neq x x;
  neq_sym : forall x y : carrier, neq x y -> neq y x;
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

#[refine]
#[export]
Instance Apartoid_to_Setoid (A : Apartoid) : Setoid A :=
{
    equiv := fun x y : A => ~ neq x y
}.
Proof.
  split; red; intros; intro; eauto.
    eapply neq_irrefl; eauto.
Abort.

Definition ApartoidHom (X Y : Apartoid) : Type :=
  {f : X -> Y | forall x x' : X, ~ neq x x' -> ~ neq (f x) (f x')}.

Definition ApartoidHom_Fun {X Y : Apartoid} (f : ApartoidHom X Y) : X -> Y := proj1_sig f.
Coercion ApartoidHom_Fun : ApartoidHom >-> Funclass.

Ltac apartoidhom f := try intros until f;
match type of f with
| ApartoidHom _ _ =>
  let a := fresh f "_pres_equiv" in destruct f as [f a]
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
  red; destruct f as [f Hf], g as [g Hg].
  exists (fun x : X => g (f x)). auto.
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
| pres_equiv : forall x x' : _, ~ ?A_neq x x' -> ~ ?B_neq (?f x) (?f x'),
  H : ~ ?A_neq ?x ?x', H' : ?B_neq (?f ?x) (?f ?x') |- False =>
  eapply pres_equiv; eauto
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
  HomSetoid := fun X Y : Apartoid =>
  {|
    equiv := fun f g : ApartoidHom X Y => forall x : X, ~ f x # g x
  |};
  comp := ApartoidComp;
  id := ApartoidId
}.
Proof.
  (* Equivalence *) solve_equiv; apartoid'.
    eapply H. apply Y_neq_sym. eauto.
    destruct (Y_neq_cotrans _ _ (y x0) H1).
      eapply H. apply Y_neq_sym. eauto.
      eapply H0. apply Y_neq_sym. eauto.
  (* Proper *) apartoid'.
    apply (C_neq_cotrans _ _ (y0 (x x1))) in H1. destruct H1.
      eapply H0. eauto.
      now eapply (y0_pres_equiv _ _ (H x1)).
  (* Category laws *) all: apartoid.
Defined.

#[refine]
#[export]
Instance Apartoid_init : Apartoid :=
{
  carrier := Empty_set;
  neq := fun (e : Empty_set) _ => match e with end
}.
Proof. all: apartoid. Defined.

Definition Apartoid_create (X : Apartoid) : ApartoidHom Apartoid_init X.
Proof.
  red. exists (fun (e : Empty_set) => match e with end). apartoid.
Defined.

#[refine]
#[export]
Instance HasInit_Apartoid : HasInit ApartoidCat :=
{
  init := Apartoid_init;
  create := Apartoid_create
}.
Proof. apartoid. Defined.

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
  red; cbn. now exists (fun _ => tt).
Defined.

#[refine]
#[export]
Instance HasTerm_Apartoid : HasTerm ApartoidCat :=
{
  term := Apartoid_term;
  delete := Apartoid_delete
}.
Proof. apartoid. Defined.

#[refine]
#[export]
Instance Apartoid_product (X Y : Apartoid) : Apartoid :=
{
  carrier := X * Y;
  neq := fun (p1 : X * Y) (p2 : X * Y) =>
    neq (fst p1) (fst p2) \/ neq (snd p1) (snd p2)
}.
Proof.
  all: destruct x; try destruct y; try destruct z; apartoid.
  apartoid_simpl; destruct H.
    destruct (neq_cotrans _ _ c3 H); auto.
    destruct (neq_cotrans _ _ c4 H); auto.
Defined.

Definition Apartoid_outl (X Y : Apartoid) : ApartoidHom (Apartoid_product X Y) X.
Proof.
  red. exists fst. apartoid.
Defined.

Definition Apartoid_outr (X Y : Apartoid) : ApartoidHom (Apartoid_product X Y) Y.
Proof.
  red. exists snd. apartoid.
Defined.

Definition Apartoid_fpair
  (A B X : Apartoid) (f : ApartoidHom X A) (g : ApartoidHom X B)
  : ApartoidHom X (Apartoid_product A B).
Proof.
  red. exists (fun x : X => (f x, g x)). apartoid.
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
Proof. apartoid. Defined.

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
  all: intros; repeat
  match goal with
  | x : _ + _ |- _ => destruct x
  | _ => apartoid
  end.
Defined.

Definition Apartoid_finl
  (X Y : Apartoid) : ApartoidHom X (Apartoid_coproduct X Y).
Proof.
  red. exists inl. apartoid.
Defined.

Definition Apartoid_finr
  (X Y : Apartoid) : ApartoidHom Y (Apartoid_coproduct X Y).
Proof.
  red. exists inr. apartoid.
Defined.

Definition Apartoid_copair
  (A B X : Apartoid) (f : ApartoidHom A X) (g : ApartoidHom B X)
  : ApartoidHom (Apartoid_coproduct A B) X.
Proof.
  red. exists (fun p : A + B =>
    match p with
    | inl a => f a
    | inr b => g b
    end).
  destruct x, x'; apartoid.
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
  split; [apartoid | apartoid |].
  intros P' [h1 h1'] [h2 h2'] Heq1 Heq2 [a | b] H; cbn in H, Heq1, Heq2.
  - now apply (Heq1 a).
  - now apply (Heq2 b).
Defined.

#[refine]
#[export]
Instance Apartoid_indexedProduct {J : Set} (A : J -> Apartoid) : Apartoid :=
{
  carrier := forall j : J, A j;
  neq := fun f g : forall j : J, A j => exists j : J, f j # g j
}.
Proof.
  intros; intro. destruct H as [j H]. now apply (neq_irrefl (x j)).
  intros. destruct H as [j H]. exists j. now apply neq_sym.
  intros. destruct H as [j H]. destruct (neq_cotrans (x j) (y j) (z j) H).
    left. now exists j.
    right. now exists j.
Defined.

Definition Apartoid_out
  {J : Set} (A : J -> Apartoid) (j : J) : ApartoidHom (Apartoid_indexedProduct A) (A j).
Proof.
  red. exists (fun (f : forall j : J, A j) => f j). intros.
  intro. apply H. simpl. now exists j.
Defined.

Definition Apartoid_tuple
  {J : Set} {A : J -> Apartoid} {X : Apartoid}
  (f : forall j : J, ApartoidHom X (A j))
  : ApartoidHom X (Apartoid_indexedProduct A).
Proof.
  red. exists (fun (x : X) (j : J) => f j x). cbn; intros.
  intro. destruct H0 as [j H']. destruct (f j) as [fj Hfj]; cbn in *.
  eapply Hfj; eauto.
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
  - eauto.
  - intros [j Hj]. apply (H j x). apartoid.
Defined.

#[refine]
#[export]
Instance Apartoid_equalizer {X Y : Apartoid} (f g : ApartoidHom X Y) : Apartoid :=
{
  carrier := {x : X | ~ (f x) # (g x)};
  neq := fun p1 p2 : {x : X | ~ (f x) # (g x)} =>
    proj1_sig p1 # proj1_sig p2
}.
Proof. all: apartoid. Defined.

Definition Apartoid_equalize
  {X Y : Apartoid} (f g : ApartoidHom X Y) : ApartoidHom (Apartoid_equalizer f g) X.
Proof.
  red; cbn. exists (@proj1_sig _ _). apartoid.
Defined.

Lemma trick
  (X Y E' : Apartoid) (f g : Hom X Y)
  (e' : Hom E' X) (H : e' .> f == e' .> g)
  : E' -> Apartoid_equalizer f g.
Proof.
  intro arg. red; cbn in *. exists (e' arg). apartoid.
Defined.

Lemma trick2
  (X Y E' : Apartoid) (f g : Hom X Y)
  (e' : Hom E' X) (H : e' .> f == e' .> g)
  : ApartoidHom E' (Apartoid_equalizer f g).
Proof.
  exists (trick X Y E' f g e' H). apartoid.
Defined.

(* This runs for about ~10 secs. *)
#[refine]
#[export]
Instance HasEqualizers_Apartoid : HasEqualizers ApartoidCat :=
{
  equalizer := @Apartoid_equalizer;
  equalize := @Apartoid_equalize;
}.
Proof.
Abort.

(* TODO: likely this can't be done at all.
Inductive Apartoid_coeq_neq {X Y : Apartoid} (f g : ApartoidHom X Y) : Y -> Y -> Prop :=
| coeq_step : forall y y' : Y, y # y' -> CoqSetoid_coeq_neq f g y y'
| coeq_quot : forall x x' : X, x # x' -> CoqSetoid_coeq_neq f g (f x) (g x')
| coeq_sym : forall y y' : Y, Apartoid_coeq_neq f g y y' -> Apartoid_coeq_neq f g y' y
| coeq_cotrans_l :
  forall y1 y2 y3 : Y,
    Apartoid_coeq_neq f g y1 y2 ->
    Apartoid_coeq_neq f g y2 y3 ->
    Apartoid_coeq_neq f g y1 y3.
*)

(* TODO: this shit doesn't work. *)
Inductive Apartoid_coeq_equiv {X Y : Apartoid} (f g : ApartoidHom X Y) : Y -> Y -> Prop :=
| coeq_step : forall y y' : Y, ~ y # y' -> Apartoid_coeq_equiv f g y y'
| coeq_quot : forall x : X, Apartoid_coeq_equiv f g (f x) (g x)
| coeq_sym : forall y y' : Y, Apartoid_coeq_equiv f g y y' -> Apartoid_coeq_equiv f g y' y
| coeq_trans :
  forall y1 y2 y3 : Y,
    Apartoid_coeq_equiv f g y1 y2 ->
    Apartoid_coeq_equiv f g y2 y3 ->
    Apartoid_coeq_equiv f g y1 y3.

(* TODO: finish *)
#[refine]
#[export]
Instance Apartoid_coequalizer {X Y : Apartoid} (f g : ApartoidHom X Y) : Apartoid :=
{
  carrier := Y;
  neq := fun y y' : Y => ~ ~ ~ Apartoid_coeq_equiv f g y y'
}.
Proof.
  intros. intro. apply H. intro. apply H0. constructor. apply neq_irrefl.
  intros. intro. apply H0. intro. apply H. intro. apply H2.
    now apply coeq_sym.
  intros.
  intros. 
    left. intro. apply H.
Abort.

Lemma JMeq_cotrans :
  forall (X Y Z : Type) (x : X) (y : Y) (z : Z),
    ~ JMeq x y -> ~ JMeq z x \/ ~ JMeq z y.
Proof.
  intros. left. intro. apply H.
Abort.

(* TODO: make this more dependent (change JMeq to some lifted heterogenous apartness... *)
#[refine]
#[export]
Instance Apartoid_indexedCoproduct {J : Apartoid} (A : J -> Apartoid) : Apartoid :=
{
  carrier := {j : J & A j};
  neq := fun p1 p2 : {j : J & A j} => projT1 p1 # projT1 p2
}.
Proof.
  all: destruct x; try destruct y; try destruct z; eauto.
Defined.

Definition Apartoid_inj
  {J : Apartoid} (A : J -> Apartoid) (j : J) : ApartoidHom (A j) (Apartoid_indexedCoproduct A).
Proof.
  red; cbn in *. exists (fun a : A j => existT _ j a); cbn.
  intros; intro. eapply neq_irrefl. eauto.
Defined.

Definition Apartoid_indexedCopair
  {J : Apartoid} {A : J -> Apartoid}
  {X : Apartoid} (f : forall j : J, ApartoidHom (A j) X)
  : ApartoidHom (Apartoid_indexedCoproduct A) X.
Proof.
  red; cbn. exists (fun p : {j : J & A j} => f (projT1 p) (projT2 p)).
  destruct x as [j a], x' as [j' a']; cbn; do 2 intro.
  destruct (f j) as [fj Hfj]; cbn in *.
  destruct (f j') as [fj' Hfj']; cbn in *.
  apply (Hfj a a).
Abort.