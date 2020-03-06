Require Export Cat.
Require Export InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.
Require Import Equalizer.

#[refine]
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
  (* Equivalence *) solve_equiv.
  (* Composition is proper *) proper. solve_depExtEq.
  (* Category laws *) all: cat.
Defined.

Theorem DepExtSet_mon_inj : forall (A B : Ob DepExtSet) (f : A -> B),
    Mon f <-> @injectiveS A B
      {| equiv := @depExtEq A A |} {| equiv := @depExtEq B B |} f.
Proof.
  unfold Mon, injectiveS; simpl; split; intros.
    change (depExtEq a a') with (depExtEq ((fun _ => a) a) ((fun _ => a') a)).
      eapply (depExtEq_unext (fun _ : A => a) (fun _ : A => a')).
        apply H. eapply depExtEq_ext. intro. assumption.
        apply (depExtEq_eq (eq_refl a)). auto.
    apply depExtEq_ext. intro. apply H.
      apply (depExtEq_unext
        (fun a : X => f (g a)) (fun a : X => f (h a)) H0 x x). auto.
Qed.

#[refine]
Instance DepExtSet_has_init : has_init DepExtSet :=
{
    init := Empty_set;
    create := fun (X : Set) (e : Empty_set) => match e with end
}.
Proof. simpl; intros. apply depExtEq_ext. destruct x. Defined.

#[refine]
Instance DepExtSet_has_term : has_term DepExtSet :=
{
    term := unit;
    delete := fun (X : Set) (x : X) => tt
}.
Proof.
  simpl; intros. apply depExtEq_ext. intro. destruct (f x). auto.
Defined.

#[refine]
Instance DepExtSet_has_products : has_products DepExtSet :=
{
    prodOb := prod;
    proj1 := @fst;
    proj2 := @snd;
    fpair := fun (A B X : Ob DepExtSet) (f : Hom X A) (g : Hom X B) =>
      fun x : X => (f x, g x)
}.
Proof.
  proper. solve_depExtEq.
  repeat (red || split); simpl; auto; destruct 1; solve_depExtEq.
    1: change (fst (y x)) with ((fun a => fst (y a)) x).
    2: change (snd (y x)) with ((fun a => snd (y a)) x).
    all: solve_depExtEq.
Defined.

(* TODO *)
#[refine]
Instance DepExtSet_has_all_products : has_all_products DepExtSet :=
{
    bigProdOb := fun (J : Set) (A : J -> Ob DepExtSet) =>
        forall j : J, A j;
    bigProj := fun (J : Set) (A : J -> Ob DepExtSet) (j : J) =>
        fun (f : forall j : J, A j) => f j;
    tuple := fun (J : Set) (A : J -> Ob DepExtSet) (X : Ob DepExtSet)
        (f : forall j : J, Hom X (A j)) (x : X) (j : J) => f j x
}.
Proof.
  (* Proper *) repeat red; simpl; intros. apply depExtEq_ext. intro.

(*    change (fun j : J => f j a) with (fun j : J => (f j) a).
    change (fun j : J => f j a) with (fun j : J => (f j) a).
*)
    change (fun j : J => f j x) with (fun j : J => (fun a : X => f j a) x).
    change (fun j : J => g j x) with (fun j : J => (fun a : X => g j a) x). admit.
  (* Universal property *) unfold big_product_skolem; simpl; intros.
    repeat (red || split).
      intro. apply depExtEq_ext. intro. auto.
      intros. apply depExtEq_ext. intro. admit.
Abort.

#[refine]
Instance DepExtSet_has_coproducts : has_coproducts DepExtSet :=
{
    coprodOb := sum;
    coproj1 := @inl;
    coproj2 := @inr;
    copair := fun (A B X : Ob DepExtSet) (f : Hom A X) (g : Hom B X) =>
      fun p : A + B => match p with
        | inl a => f a
        | inr b => g b
      end
}.
Proof.
  (* codiag is proper *) proper. solve_depExtEq; destruct x1; solve_depExtEq.
  (* Coproduct law *) red; my_simpl; simpl; intros; solve_depExtEq.
    destruct H, x.
      match goal with
          | H : depExtEq ?f _ |- depExtEq (?f ?x) _ =>
              idtac f; idtac x
      end.
      apply (depExtEq_unext _ _ H a a). auto.
      apply (depExtEq_unext _ _ H0 b b). auto.
Defined.

#[refine]
Instance DepExtSet_has_all_coproducts : has_all_coproducts DepExtSet :=
{
    bigCoprodOb := fun (J : Set) (A : J -> Ob DepExtSet) =>
        {j : J & A j};
    bigCoproj := fun (J : Set) (A : J -> Ob DepExtSet) (j : J) =>
        fun (x : A j) => existT A j x;
    cotuple := fun (J : Set) (A : J -> Ob DepExtSet) (X : Ob DepExtSet)
        (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) =>
          f (projT1 p) (projT2 p)
}.
Proof.
  (* cotuple is proper *) simpl; intros; solve_depExtEq.
    destruct x; simpl; solve_depExtEq.
    apply (depExtEq_unext _ _ (H x) a a). auto.
  (* Coproduct law *) red; my_simpl; simpl; intros; solve_depExtEq.
    destruct x; simpl.
    apply (depExtEq_unext _ _ (H x)). auto.
Defined.

Set Nested Proofs Allowed.

(* TODO *)
#[refine]
Instance DepExtSet_has_equalizers : has_equalizers DepExtSet :=
{
    eq_ob := fun (X Y : Ob DepExtSet) (f g : Hom X Y) =>
        {x : X | depExtEq (f x) (g x)};
    eq_mor := fun (X Y : Ob DepExtSet) (f g : Hom X Y) =>
        fun (x : {x : X | depExtEq (f x) (g x)}) => proj1_sig x
}.
Proof.
  unfold equalizer; simpl; split; intros.
    apply depExtEq_ext. destruct x as [x eq]; simpl. assumption.
    Lemma trick : forall (X Y E' : Set) (f g : X -> Y) (e' : E' -> X)
      (H : depExtEq (fun a : E' => f (e' a)) (fun a : E' => g (e' a))),
      E' -> {x : X | depExtEq (f x) (g x)}.
    Proof.
      intros. exists (e' H0). apply (depExtEq_unext _ _ H). reflexivity.
    Defined.
    exists (trick _ _ _ f g e' H). repeat (red || split); intros.
      simpl. apply depExtEq_ext. auto.
      apply depExtEq_ext. intro. destruct (y x).
      unfold trick.
Abort.

(* TODO: looks like DepExtSet won't have coequalizers. *)