From Cat Require Import Cat.
From Cat.Limits Require Import InitTerm BinProdCoprod BigProdCoprod Equalizer.

Inductive extEq : forall A : Type, A -> A -> Prop :=
| extEq_refl :
  forall (A : Type) (x : A),
    extEq A x x
| extEq_sym :
  forall (A : Type) (x y : A),
    extEq A x y -> extEq A y x
| extEq_trans :
  forall (A : Type) (x y z : A),
    extEq A x y -> extEq A y z -> extEq A x z
| extEq_ext :
  forall (A B : Type) (f g : A -> B),
    (forall a : A, extEq B (f a) (g a)) -> extEq (A -> B) f g
| extEq_unext :
  forall (A B : Type) (f g : A -> B),
    extEq (A -> B) f g -> forall x y : A, extEq A x y -> extEq B (f x) (g y).

Arguments extEq [A] _ _.

#[global] Hint Constructors extEq : core.

#[export]
Instance extEq_Equivalence (A : Type) : Equivalence (@extEq A).
Proof. split; eauto. Defined.

#[export]
Instance extEq_Proper :
  forall (A B : Type) (f : A -> B),
    Proper (@extEq A ==> @extEq B) f.
Proof.
  repeat red; intros. induction H; subst.
    auto.
    eapply extEq_trans; eauto.
    eapply extEq_trans; eauto.
    apply extEq_unext; auto.
    apply extEq_unext; auto.
Defined.

#[export]
Instance extEq_Proper' :
  forall (A B : Type) (f : A -> B),
    Proper (@extEq A --> @extEq B) f.
Proof.
  repeat red; intros. induction H; subst.
    auto.
    eapply extEq_trans; eauto.
    eapply extEq_trans; eauto.
    apply extEq_unext; auto.
    apply extEq_unext; auto.
Defined.

#[export]
Instance extEq_Proper'' :
  forall (A : Type),
    Proper (@extEq A ==> @extEq A ==> (Basics.flip Basics.impl)) (@extEq A).
Proof.
  repeat red. intros. eapply extEq_trans. eauto. eauto.
Defined.

#[refine]
#[export]
Instance ExtSet : Cat :=
{|
  Ob := Type;
  Hom := fun A B : Type => A -> B;
  HomSetoid := fun A B : Type => {| equiv := fun f g : A -> B => extEq f g |};
  comp := fun (A B C : Type) (f : A -> B) (g : B -> C) (a : A) => g (f a);
  id := fun (A : Type) (a : A) => a
|}.
Proof.
  (* Equivalence *) solve_equiv.
  (* Composition is proper *) proper.
  (* Category laws *) all: cat.
Defined.

Lemma ExtSet_mon_inj :
  forall (A B : Ob ExtSet) (f : A -> B),
    Mon f <-> @injectiveS A B {| equiv := @extEq A |} {| equiv := @extEq B |} f.
Proof.
  unfold Mon, injectiveS; cbn; split; intros.
    change (extEq a a') with (extEq ((fun _ => a) a) ((fun _ => a') a)).
      apply extEq_unext. apply H. apply extEq_ext. intro. assumption. auto.
    apply extEq_ext. intro. apply H.
      apply (extEq_unext X B
        (fun a : X => f (g a)) (fun a : X => f (h a)) H0 a a). auto.
Qed.

Lemma ExtSet_ret_surjective :
  forall (A B : Type) (f : Hom A B), {g : Hom B A | g .> f = id B} ->
    @surjectiveS A B {| equiv := @extEq B |} f.
Proof.
  intros until f; intro H. red.
    destruct H as [g H]. intro. exists (g b). cbn in *.
    change (f (g b)) with ((fun a : B => (f (g a))) b).
    change b with ((fun a : B => a) b) at 2.
    rewrite H. reflexivity.
Qed.

Lemma ExtSet_surjective_ret :
  forall (A B : Type) (f : Hom A B),
    @surjectiveS A B {| equiv := @extEq B |} f ->
      {g : Hom B A | g .> f == id B}.
Proof.
  intros. red in H.
  exists (fun b => proj1_sig (constructive_indefinite_description _ (H b))).
  simpl. apply extEq_ext. intro b.
  destruct (constructive_indefinite_description (fun a : A => extEq (f a) b) (H b)).
  simpl. assumption.
Qed.

#[refine]
#[export]
Instance ExtSet_has_init : has_init ExtSet :=
{
  init := Empty_set;
  create := fun (X : Type) (e : Empty_set) => match e with end
}.
Proof. cbn; intros. apply extEq_ext. destruct a. Defined.

#[refine]
#[export]
Instance ExtSet_has_term : has_term ExtSet :=
{
  term := unit;
  delete := fun (X : Type) (x : X) => tt
}.
Proof.
  cbn; intros. apply extEq_ext. intro. destruct (f a). auto.
Defined.

#[refine]
#[export]
Instance ExtSet_has_products : has_products ExtSet :=
{
  prodOb := prod;
  proj1 := @fst;
  proj2 := @snd;
  fpair := fun (A B X : Ob ExtSet) (f : Hom X A) (g : Hom X B) =>
    fun x : X => (f x, g x)
}.
Proof.
  repeat red; cbn; intros. apply extEq_ext. intro. cat.
  repeat (red || split); cbn.
    apply extEq_ext. auto.
    apply extEq_ext. auto.
    destruct 1. apply extEq_ext. intros.
      assert (extEq (f a) (fst (y a))).
        apply (extEq_unext X A f (fun a : X => fst (y a)) H a a). auto.
      assert (extEq (g a) (snd (y a))).
        apply (extEq_unext X B g (fun a : X => snd (y a)) H0 a a). auto.
      destruct (y a); cbn in *. auto.
Defined.

(* TODO *)
#[refine]
#[export]
Instance ExtSet_has_all_products : has_all_products ExtSet :=
{
  bigProdOb := fun (J : Type) (A : J -> Ob ExtSet) => forall j : J, A j;
  bigProj := fun (J : Type) (A : J -> Ob ExtSet) (j : J) => fun (f : forall j : J, A j) => f j;
  tuple :=
    fun (J : Type) (A : J -> Ob ExtSet) (X : Ob ExtSet)
        (f : forall j : J, Hom X (A j)) (x : X) (j : J) => f j x
}.
Proof.
  (* Proper *) repeat red; cbn; intros. apply extEq_ext. intro.
  (* extEq *) admit.
  (* Universal property *) unfold big_product_skolem; cbn; intros.
    repeat (red || split).
      intro. apply extEq_ext. intro. auto.
      intros. apply extEq_ext. intro. cbn in *.
      change (y a) with (fun j => y a j).
Abort.

#[refine]
#[export]
Instance ExtSet_has_coproducts : has_coproducts ExtSet :=
{
  coprodOb := sum;
  coproj1 := @inl;
  coproj2 := @inr;
  copair := fun (A B X : Ob ExtSet) (f : Hom A X) (g : Hom B X) =>
    fun p : A + B =>
    match p with
    | inl a => f a
    | inr b => g b
    end
}.
Proof.
  (* copair is proper *) proper. apply extEq_ext; intros. destruct a; cat.
  (* Coproduct law *) red; cat. apply extEq_ext; intros. destruct a; cat.
Defined.

#[refine]
#[export]
Instance ExtSet_has_all_coproducts : has_all_coproducts ExtSet :=
{
  bigCoprodOb := fun (J : Type) (A : J -> Ob ExtSet) => {j : J & A j};
  bigCoproj := fun (J : Type) (A : J -> Ob ExtSet) (j : J) => fun (x : A j) => existT A j x;
  cotuple :=
    fun (J : Type) (A : J -> Ob ExtSet) (X : Ob ExtSet)
      (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) =>
        f (projT1 p) (projT2 p)
}.
Proof.
  (* cotuple is proper *) cat.
  (* Coproduct law *) red; cat. apply extEq_ext. cat.
Defined.

Set Nested Proofs Allowed.

(* TODO *)
#[refine]
#[export]
Instance ExtSet_has_equalizers : has_equalizers ExtSet :=
{
  eq_ob := fun (X Y : Ob ExtSet) (f g : Hom X Y) => {x : X | extEq (f x) (g x)};
  eq_mor :=
    fun (X Y : Ob ExtSet) (f g : Hom X Y) =>
      fun (x : {x : X | extEq (f x) (g x)}) => proj1_sig x
}.
Proof.
Abort.