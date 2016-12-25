Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Cat.
Require Export InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.
Require Import Equalizer.

Require Export Equivalences.

Instance DepExtSet : Cat :=
{|
    Ob := Set;
    Hom := fun A B : Set => A -> B;
    HomSetoid := fun A B : Set =>
        {| equiv := fun f g : A -> B => depExtEq f g |};
    comp := fun (A B C : Set) (f : A -> B) (g : B -> C) (a : A) => g (f a);
    id := fun (A : Set) (a : A) => a
|}.
Proof.
  (* Equivalence *) split; eauto.
  (* Composition is proper *) repeat (red || split); simpl. intros.
    solve_depExtEq.
  (* Category laws *) all: cat.
Defined.

Theorem DepExtSet_mon_inj : forall (A B : Ob DepExtSet) (f : A -> B),
    Mon f <-> @injectiveS A B
      {| equiv := @depExtEq A A |} {| equiv := @depExtEq B B |} f.
Proof.
  unfold Mon, injectiveS; simpl; split; intros.
    change (depExtEq a a') with (depExtEq ((fun _ => a) a) ((fun _ => a') a)).
      eapply (depExtEq_unext _ _ _ (fun _ : A => a) (fun _ : A => a')).
      apply H. eapply depExtEq_ext.
        intro. assumption.
        apply (depExtEq_eq _ a a). auto.
    apply depExtEq_ext. intro. apply H.
      apply (depExtEq_unext _ _ _
        (fun a : X => f (g a)) (fun a : X => f (h a)) H0 x x). auto.
Qed.

Instance DepExtSet_has_init : has_init DepExtSet :=
{
    init := Empty_set;
    create := fun (X : Set) (e : Empty_set) => match e with end
}.
Proof. simpl; intros. apply depExtEq_ext. destruct x. Defined.

Instance DepExtSet_has_term : has_term DepExtSet :=
{
    term := unit;
    delete := fun (X : Set) (x : X) => tt
}.
Proof.
  simpl; intros. apply depExtEq_ext. intro. destruct (f x). auto.
Defined.

Instance DepExtSet_has_products : has_products DepExtSet :=
{
    prodOb := prod;
    proj1 := @fst;
    proj2 := @snd;
    diag := fun (A B X : Ob DepExtSet) (f : Hom X A) (g : Hom X B) =>
      fun x : X => (f x, g x)
}.
Proof.
  repeat red; simpl; intros. apply depExtEq_ext. intro.
    apply (depExtEq_unext' _ _ _ _ (pair (x x1)) (pair (y x1))).
      apply (depExtEq_unext' _ _ _ _ pair pair). auto.
        apply (depExtEq_unext' _ _ _ _ x y). auto. auto.
      apply (depExtEq_unext' _ _ _ _ x0 y0). auto. auto.
  repeat (red || split); simpl.
    apply depExtEq_ext. auto.
    apply depExtEq_ext. auto.
    destruct 1. apply depExtEq_ext. intros.
      assert (depExtEq (f x) (fst (y x))).
        apply (depExtEq_unext _ _ _ f (fun a : X => fst (y a)) H x x). auto.
      assert (depExtEq (g x) (snd (y x))).
        apply (depExtEq_unext _ _ _ g (fun a : X => snd (y a)) H0 x x). auto.
      destruct (y x); simpl in *.
      apply (depExtEq_unext' _ _ _ _ (pair (f x)) (pair a)).
        apply (depExtEq_unext' _ _ _ _ pair pair). auto. auto. auto.      
Defined.

Instance DepExtSet_has_all_products : has_all_products DepExtSet :=
{
    bigProdOb := fun (J : Set) (A : J -> Ob DepExtSet) =>
        forall j : J, A j;
    bigProj := fun (J : Set) (A : J -> Ob DepExtSet) (j : J) =>
        fun (f : forall j : J, A j) => f j;
    bigDiag := fun (J : Set) (A : J -> Ob DepExtSet) (X : Ob DepExtSet)
        (f : forall j : J, Hom X (A j)) (x : X) (j : J) => f j x
}.
Proof.
  (* Proper *) repeat red; simpl; intros. apply depExtEq_ext. intro. Print depExtEq.

(*    change (fun j : J => f j a) with (fun j : J => (f j) a).
    change (fun j : J => f j a) with (fun j : J => (f j) a).
*)
    change (fun j : J => f j a) with (fun j : J => (fun a : X => f j a) a).
    change (fun j : J => g j a) with (fun j : J => (fun a : X => g j a) a). admit.
    Print depExtEq_ext.
  (* Universal property *) unfold big_product_skolem; simpl; intros.
    repeat (red || split).
      intro. apply depExtEq_ext. intro. auto.
      intros. apply depExtEq_ext. intro. Print depExtEq. apply depExtEq_unext.
      
Defined.

Instance DepExtSet_has_coproducts : has_coproducts DepExtSet :=
{
    coprodOb := sum;
    coproj1 := @inl;
    coproj2 := @inr;
    codiag := fun (A B X : Ob DepExtSet) (f : Hom A X) (g : Hom B X) =>
      fun p : A + B => match p with
        | inl a => f a
        | inr b => g b
      end
}.
Proof.
  all: repeat red; cat;
  match goal with | x : _ + _ |- _ => destruct x end; cat.
Defined.

Instance DepExtSet_has_all_coproducts : has_all_coproducts DepExtSet :=
{
    bigCoprodOb := fun (J : Set) (A : J -> Ob DepExtSet) =>
        {j : J & A j};
    bigCoproj := fun (J : Set) (A : J -> Ob DepExtSet) (j : J) =>
        fun (x : A j) => existT A j x;
    bigCodiag := fun (J : Set) (A : J -> Ob DepExtSet) (X : Ob DepExtSet)
        (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) =>
          f (projT1 p) (projT2 p)
}.
Proof.
  simpl; intros.
  cat. destruct x. cat.
Defined.

Theorem DepExtSet_ret_invertible : forall (A B : Set)
    (f : Hom A B), {g : Hom B A | g .> f = id B} ->
    invertible {| equiv := eq |} f.
Proof.
  intros. red.
    destruct H as [g H]. intro. exists (g b). simpl in *.
    change (f (g b)) with ((fun a : B => (f (g a))) b).
    change b with ((fun a : B => a) b) at 2.
    rewrite H. auto.
Qed.

Theorem DepExtSet_invertible_ret : forall (A B : Set) (f : Hom A B),
    invertible {| equiv := eq |} f -> {g : Hom B A | g .> f == id B}.
Proof.
  intros. red in H.
  exists (fun b => proj1_sig (H b)). simpl.
  intro b. destruct (H b). simpl in *. auto.
Qed.

Theorem DepExtSet_counterexample1 :
    exists (A B C : Set) (f : Hom A B) (g : Hom B C),
    injective (f .> g) /\ ~ (injective g).
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold injective, not; simpl; split; intros.
    destruct x, y; auto.
    specialize (H true false eq_refl). discriminate H.
Qed.

Theorem DepExtSet_counterexample2 : exists (A B C : Set) (f : Hom A B)
    (g : Hom B C), surjective (f .> g) /\ ~ (surjective f).
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold surjective, not; simpl; split; intros.
    exists tt. destruct b. auto.
    destruct (H false). inversion H0.
Qed.

(* It's time to change all this shit to be constructive and proof-relevant. *)
Theorem DepExtSet_iso_bij : forall (A B : Set) (f : Hom A B),
    Iso f -> injective f /\ surjective f.
Proof.
  unfold injective, surjective, Iso; simpl; intros. split; intros.
    destruct H as [g [H1 H2]]. rewrite <- (H1 x), <- (H1 y).
      rewrite H0. auto.
    destruct H as [g [H1 H2]]. exists (g b). rewrite H2. auto.
Defined.

(* Case analysis on sort Set. *)
(*Theorem DepExtSet_iso_bin_conv : forall (A B : Set) (f : Hom A B),
    injective f -> surjective f -> Iso f.
Proof.
  unfold injective, surjective, Iso. intros.
  assert (g : B -> A).
    intro b. Focus 2.
    exists g. simpl; split; intros.
      destruct (H0 (f x)).
*)

Instance DepExtSet_has_equalizers : has_equalizers DepExtSet :=
{
    eq_ob := fun (X Y : Ob DepExtSet) (f g : Hom X Y) =>
        {x : X | f x = g x};
    eq_mor := fun (X Y : Ob DepExtSet) (f g : Hom X Y) =>
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
(*Instance DepExtSet_has_coequalizers : has_coequalizers DepExtSet :=
{
    coeq_ob := fun (X Y : Ob DepExtSet) (f g : Hom X Y) =>
        {T : Set & {y : Y | T = {y' : Y | exists x : X, f x = y /\ g x = y /\ y = y'}}}
    (*coeq_mor := fun (X Y : Ob DepExtSet) (f g : Hom X Y) =>*)
        
}.
Proof.
  simpl; intros X Y f g y. exists {A : {y : Y | 
  unfold coequalizer; simpl; intros. cat. f_equal.
*) *)