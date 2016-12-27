Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Cat.
Require Export InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.
Require Import Equalizer.

Require Export Equivalences.

(*Instance extSet : Cat :=
{|
    Ob := Set;
    Hom := fun A B : Set => A -> B;
    HomSetoid := fun A B : Set =>
        {| equiv := @ext (A -> B) |};
    comp := fun (A B C : Set) (f : A -> B) (g : B -> C) (a : A) => g (f a);
    id := fun (A : Set) (a : A) => a
|}.
Proof.
  apply ext_Equivalence.
  (* Composition is proper *) repeat (red || split); simpl. intros.
    apply ext_ext. intro. rewrite H.
  (* Category laws *) all: cat.
Defined.
*)

Instance ExtSet : Cat :=
{|
    Ob := Set;
    Hom := fun A B : Set => A -> B;
    HomSetoid := fun A B : Set =>
        {| equiv := fun f g : A -> B => extEq f g |};
    comp := fun (A B C : Set) (f : A -> B) (g : B -> C) (a : A) => g (f a);
    id := fun (A : Set) (a : A) => a
|}.
Proof.
  (* Equivalence *) split; eauto.
  (* Composition is proper *) repeat (red || split); simpl. intros.
    apply extEq_ext. intro. apply extEq_unext. assumption.
    apply extEq_unext. assumption. auto.
  (* Category laws *) all: cat.
Defined.

Theorem ExtSet_mon_inj : forall (A B : Ob ExtSet) (f : A -> B),
    Mon f <-> @injectiveS A B {| equiv := @extEq A |} {| equiv := @extEq B |} f.
Proof.
  unfold Mon, injectiveS; simpl; split; intros.
    change (extEq a a') with (extEq ((fun _ => a) a) ((fun _ => a') a)).
      apply extEq_unext. apply H. apply extEq_ext. intro. assumption. auto.
    apply extEq_ext. intro. apply H.
      apply (extEq_unext X B
        (fun a : X => f (g a)) (fun a : X => f (h a)) H0 a a). auto.
Qed.

Instance ExtSet_has_init : has_init ExtSet :=
{
    init := Empty_set;
    create := fun (X : Set) (e : Empty_set) => match e with end
}.
Proof. simpl; intros. apply extEq_ext. destruct a. Defined.

Instance ExtSet_has_term : has_term ExtSet :=
{
    term := unit;
    delete := fun (X : Set) (x : X) => tt
}.
Proof.
  simpl; intros. apply extEq_ext. intro. destruct (f a). auto.
Defined.

Instance ExtSet_has_products : has_products ExtSet :=
{
    prodOb := prod;
    proj1 := @fst;
    proj2 := @snd;
    diag := fun (A B X : Ob ExtSet) (f : Hom X A) (g : Hom X B) =>
      fun x : X => (f x, g x)
}.
Proof.
  repeat red; simpl; intros. apply extEq_ext. intro. cat. (* TODO *)
  repeat (red || split); simpl.
    apply extEq_ext. auto.
    apply extEq_ext. auto.
    destruct 1. apply extEq_ext. intros.
      assert (extEq (f a) (fst (y a))).
        apply (extEq_unext X A f (fun a : X => fst (y a)) H a a). auto.
      assert (extEq (g a) (snd (y a))).
        apply (extEq_unext X B g (fun a : X => snd (y a)) H0 a a). auto.
      destruct (y a); simpl in *. auto.
Defined.

Print ExtSet_has_products.

Instance ExtSet_has_all_products : has_all_products ExtSet :=
{
    bigProdOb := fun (J : Set) (A : J -> Ob ExtSet) =>
        forall j : J, A j;
    bigProj := fun (J : Set) (A : J -> Ob ExtSet) (j : J) =>
        fun (f : forall j : J, A j) => f j;
    bigDiag := fun (J : Set) (A : J -> Ob ExtSet) (X : Ob ExtSet)
        (f : forall j : J, Hom X (A j)) (x : X) (j : J) => f j x
}.
Proof.
  (* Proper *) repeat red; simpl; intros. apply extEq_ext. intro. Print extEq.

(*    change (fun j : J => f j a) with (fun j : J => (f j) a).
    change (fun j : J => f j a) with (fun j : J => (f j) a).
*)
    change (fun j : J => f j a) with (fun j : J => (fun a : X => f j a) a).
    change (fun j : J => g j a) with (fun j : J => (fun a : X => g j a) a). admit.
    Print extEq_ext.
  (* Universal property *) unfold big_product_skolem; simpl; intros.
    repeat (red || split).
      intro. apply extEq_ext. intro. auto.
      intros. apply extEq_ext. intro. Print extEq. apply extEq_unext.
      
Defined.

Instance ExtSet_has_coproducts : has_coproducts ExtSet :=
{
    coprodOb := sum;
    coproj1 := @inl;
    coproj2 := @inr;
    codiag := fun (A B X : Ob ExtSet) (f : Hom A X) (g : Hom B X) =>
      fun p : A + B => match p with
        | inl a => f a
        | inr b => g b
      end
}.
Proof.
  all: repeat red; cat;
  match goal with | x : _ + _ |- _ => destruct x end; cat.
Defined.

Instance ExtSet_has_all_coproducts : has_all_coproducts ExtSet :=
{
    bigCoprodOb := fun (J : Set) (A : J -> Ob ExtSet) =>
        {j : J & A j};
    bigCoproj := fun (J : Set) (A : J -> Ob ExtSet) (j : J) =>
        fun (x : A j) => existT A j x;
    bigCodiag := fun (J : Set) (A : J -> Ob ExtSet) (X : Ob ExtSet)
        (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) =>
          f (projT1 p) (projT2 p)
}.
Proof.
  simpl; intros.
  cat. destruct x. cat.
Defined.

Theorem ExtSet_ret_invertible : forall (A B : Set)
    (f : Hom A B), {g : Hom B A | g .> f = id B} ->
    invertible {| equiv := eq |} f.
Proof.
  intros. red.
    destruct H as [g H]. intro. exists (g b). simpl in *.
    change (f (g b)) with ((fun a : B => (f (g a))) b).
    change b with ((fun a : B => a) b) at 2.
    rewrite H. auto.
Qed.

Theorem ExtSet_invertible_ret : forall (A B : Set) (f : Hom A B),
    invertible {| equiv := eq |} f -> {g : Hom B A | g .> f == id B}.
Proof.
  intros. red in H.
  exists (fun b => proj1_sig (H b)). simpl.
  intro b. destruct (H b). simpl in *. auto.
Qed.

Theorem ExtSet_counterexample1 :
    exists (A B C : Set) (f : Hom A B) (g : Hom B C),
    injective (f .> g) /\ ~ (injective g).
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold injective, not; simpl; split; intros.
    destruct x, y; auto.
    specialize (H true false eq_refl). discriminate H.
Qed.

Theorem ExtSet_counterexample2 : exists (A B C : Set) (f : Hom A B)
    (g : Hom B C), surjective (f .> g) /\ ~ (surjective f).
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold surjective, not; simpl; split; intros.
    exists tt. destruct b. auto.
    destruct (H false). inversion H0.
Qed.

(* It's time to change all this shit to be constructive and proof-relevant. *)
Theorem ExtSet_iso_bij : forall (A B : Set) (f : Hom A B),
    Iso f -> injective f /\ surjective f.
Proof.
  unfold injective, surjective, Iso; simpl; intros. split; intros.
    destruct H as [g [H1 H2]]. rewrite <- (H1 x), <- (H1 y).
      rewrite H0. auto.
    destruct H as [g [H1 H2]]. exists (g b). rewrite H2. auto.
Defined.

(* Case analysis on sort Set. *)
(*Theorem ExtSet_iso_bin_conv : forall (A B : Set) (f : Hom A B),
    injective f -> surjective f -> Iso f.
Proof.
  unfold injective, surjective, Iso. intros.
  assert (g : B -> A).
    intro b. Focus 2.
    exists g. simpl; split; intros.
      destruct (H0 (f x)).
*)

Instance ExtSet_has_equalizers : has_equalizers ExtSet :=
{
    eq_ob := fun (X Y : Ob ExtSet) (f g : Hom X Y) =>
        {x : X | f x = g x};
    eq_mor := fun (X Y : Ob ExtSet) (f g : Hom X Y) =>
        fun (x : {x : X | f x = g x}) => proj1_sig x
}.
Proof.
  unfold equalizer; simpl; split; intros.
    destruct x; simpl. auto. Print sig.
    exists (fun x : E' => exist (fun x : X => f x = g x) (e' x) (H x)).
    cat. specialize (H0 x). destruct (y x). simpl in *. subst.
    f_equal. apply proof_irrelevance.
Defined.

(* Not sure if it's even true *)
(*Instance ExtSet_has_coequalizers : has_coequalizers ExtSet :=
{
    coeq_ob := fun (X Y : Ob ExtSet) (f g : Hom X Y) =>
        {T : Set & {y : Y | T = {y' : Y | exists x : X, f x = y /\ g x = y /\ y = y'}}}
    (*coeq_mor := fun (X Y : Ob ExtSet) (f g : Hom X Y) =>*)
        
}.
Proof.
  simpl; intros X Y f g y. exists {A : {y : Y | 
  unfold coequalizer; simpl; intros. cat. f_equal.
*) *)