From Cat Require Export Cat.
From Cat.Limits Require Export InitTerm ProdCoprod IndexedProdCoprod Equalizer.

Inductive depExtEq : forall A B : Type, A -> B -> Prop :=
| depExtEq_eq :
  forall (A : Type) (x y : A),
    x = y -> depExtEq A A x y
| depExtEq_sym :
  forall (A B : Type) (x : A) (y : B),
    depExtEq A B x y -> depExtEq B A y x
| depExtEq_trans :
  forall (A B C : Type) (x : A) (y : B) (z : C),
    depExtEq A B x y -> depExtEq B C y z -> depExtEq A C x z
| depExtEq_ext :
  forall (A : Type) (B C : A -> Type)
    (f : forall x : A, B x) (g : forall x : A, C x),
    (forall x : A, depExtEq (B x) (C x) (f x) (g x)) ->
      depExtEq (forall x : A, B x) (forall x : A, C x) f g
| depExtEq_unext :
  forall
    (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type)
    (f : forall x : A1, B1 x) (g : forall x : A2, B2 x),
      depExtEq (forall x : A1, B1 x) (forall x : A2, B2 x) f g ->
      forall (x : A1) (y : A2), depExtEq A1 A2 x y ->
        depExtEq (B1 x) (B2 y) (f x) (g y).

Arguments depExtEq [A B] _ _.
Arguments depExtEq_eq [A x y] _.
Arguments depExtEq_ext [A B C] _ _ _.
Arguments depExtEq_unext [A1 A2 B1 B2] _ _ _ _ _ _.

#[global] Hint Constructors depExtEq : core.

#[export]
Instance depExtEq_Equivalence (A : Type) : Equivalence (@depExtEq A A).
Proof.
  split; red; cbn; intros; eauto.
Defined.

Ltac solve_depExtEq := repeat
match goal with
| |- depExtEq (fun _ => _) _ => apply depExtEq_ext; intro
| |- depExtEq _ (fun _ => _) => apply depExtEq_ext; intro
end; auto;
repeat (auto; match goal with
| |- depExtEq (fun _ => _) (fun _ => _) => apply depExtEq_ext; intro
| H : depExtEq ?f ?g |- depExtEq (?f _ _ _) (?g _ _ _) =>
  apply (depExtEq_unext (f _ _) (g _ _))
| H : depExtEq ?f ?g |- depExtEq (?f _ _) (?g _ _) =>
  apply (depExtEq_unext (f _) (g _))
| H : depExtEq ?f ?g |- depExtEq (?f _) (?g _) =>
  apply (depExtEq_unext f g)
| |- depExtEq (?f _ _) (?f _ _) => apply (depExtEq_unext (f _) (f _))
| |- depExtEq (?f _) (?f _) => apply (depExtEq_unext f f)
| |- depExtEq (_, _) ?x => rewrite (surjective_pairing x)
end); auto.

#[export]
Instance depExtEq_Proper :
  forall (A B : Type) (f : A -> B),
    Proper (@depExtEq A A ==> @depExtEq B B) f.
Proof.
  unfold Proper, respectful; intros. solve_depExtEq.
Qed.

#[export]
Instance depExtEq_Proper' :
  forall A : Type,
    Proper (@depExtEq A A ==> @depExtEq A A ==> (Basics.flip Basics.impl)) (@depExtEq A A).
Proof.
  repeat red. intros. eapply depExtEq_trans; eauto.
Defined.

#[refine]
#[export]
Instance DepExtSet : Cat :=
{|
  Ob := Set;
  Hom := fun A B : Set => A -> B;
  HomSetoid := fun A B : Set => {| equiv := fun f g : A -> B => depExtEq f g |};
  comp := fun (A B C : Set) (f : A -> B) (g : B -> C) (a : A) => g (f a);
  id := fun (A : Set) (a : A) => a
|}.
Proof.
  (* Equivalence *) solve_equiv.
  (* Composition is proper *) proper. solve_depExtEq.
  (* Category laws *) all: cat.
Defined.

Lemma DepExtSet_mon_inj :
  forall (A B : Ob DepExtSet) (f : A -> B),
    Mon f <-> @injectiveS A B {| equiv := @depExtEq A A |} {| equiv := @depExtEq B B |} f.
Proof.
  unfold Mon, injectiveS; cbn; split; intros.
    change (depExtEq a a') with (depExtEq ((fun _ => a) a) ((fun _ => a') a)).
      eapply (depExtEq_unext (fun _ : A => a) (fun _ : A => a')).
        apply H. eapply depExtEq_ext. intro. assumption.
        apply (depExtEq_eq (eq_refl a)). auto.
    apply depExtEq_ext. intro. apply H.
      apply (depExtEq_unext
        (fun a : X => f (g a)) (fun a : X => f (h a)) H0 x x). auto.
Qed.

#[refine]
#[export]
Instance DepExtSet_HasInit : HasInit DepExtSet :=
{
  init := Empty_set;
  create := fun (X : Set) (e : Empty_set) => match e with end
}.
Proof. cbn; intros. apply depExtEq_ext. destruct x. Defined.

#[refine]
#[export]
Instance DepExtSet_HasTerm : HasTerm DepExtSet :=
{
  term := unit;
  delete := fun (X : Set) (x : X) => tt
}.
Proof.
  cbn; intros. apply depExtEq_ext. intro. destruct (f x). auto.
Defined.

#[refine]
#[export]
Instance DepExtSet_HasProducts : HasProducts DepExtSet :=
{
  prodOb := prod;
  proj1 := @fst;
  proj2 := @snd;
  fpair := fun (A B X : Ob DepExtSet) (f : Hom X A) (g : Hom X B) =>
    fun x : X => (f x, g x)
}.
Proof.
  proper. solve_depExtEq.
  repeat (red || split); cbn; auto; destruct 1; solve_depExtEq.
    1: change (fst (y x)) with ((fun a => fst (y a)) x).
    2: change (snd (y x)) with ((fun a => snd (y a)) x).
    all: solve_depExtEq.
Defined.

(* TODO *)
#[refine]
#[export]
Instance DepExtSet_HasIndexedProducts : HasIndexedProducts DepExtSet :=
{
  indexedProdOb := fun (J : Set) (A : J -> Ob DepExtSet) => forall j : J, A j;
  indexedProj := fun (J : Set) (A : J -> Ob DepExtSet) (j : J) => fun (f : forall j : J, A j) => f j;
  tuple :=
    fun (J : Set) (A : J -> Ob DepExtSet) (X : Ob DepExtSet)
        (f : forall j : J, Hom X (A j)) (x : X) (j : J) => f j x
}.
Proof.
  (* Proper *) repeat red; cbn; intros. apply depExtEq_ext. intro.
    change (fun j : J => f j x) with (fun j : J => (fun a : X => f j a) x).
    change (fun j : J => g j x) with (fun j : J => (fun a : X => g j a) x). admit.
  (* Universal property *) unfold indexed_product_skolem; cbn; intros.
    repeat (red || split).
      intro. apply depExtEq_ext. intro. auto.
      intros. apply depExtEq_ext. intro. admit.
Abort.

#[refine]
#[export]
Instance DepExtSet_HasCoproducts : HasCoproducts DepExtSet :=
{
  coprodOb := sum;
  coproj1 := @inl;
  coproj2 := @inr;
  copair :=
    fun (A B X : Ob DepExtSet) (f : Hom A X) (g : Hom B X) =>
      fun p : A + B =>
      match p with
      | inl a => f a
      | inr b => g b
      end
}.
Proof.
  (* codiag is proper *) proper. solve_depExtEq; destruct x1; solve_depExtEq.
  (* Coproduct law *) red; my_simpl; cbn; intros; solve_depExtEq.
    destruct H, x.
      apply (depExtEq_unext _ _ H a a). auto.
      apply (depExtEq_unext _ _ H0 b b). auto.
Defined.

#[refine]
#[export]
Instance DepExtSet_HasIndexedCoproducts : HasIndexedCoproducts DepExtSet :=
{
  indexedCoprodOb := fun (J : Set) (A : J -> Ob DepExtSet) => {j : J & A j};
  indexedCoproj := fun (J : Set) (A : J -> Ob DepExtSet) (j : J) => fun (x : A j) => existT A j x;
  cotuple :=
    fun (J : Set) (A : J -> Ob DepExtSet) (X : Ob DepExtSet)
        (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) =>
          f (projT1 p) (projT2 p)
}.
Proof.
  (* cotuple is proper *) cbn; intros; solve_depExtEq.
    destruct x; cbn; solve_depExtEq.
    apply (depExtEq_unext _ _ (H x) a a). auto.
  (* Coproduct law *) red; my_simpl; cbn; intros; solve_depExtEq.
    destruct x; cbn.
    apply (depExtEq_unext _ _ (H x)). auto.
Defined.

Set Nested Proofs Allowed.

(* TODO *)
#[refine]
#[export]
Instance DepExtSet_HasEqualizers : HasEqualizers DepExtSet :=
{
  eq_ob := fun (X Y : Ob DepExtSet) (f g : Hom X Y) =>
    {x : X | depExtEq (f x) (g x)};
  eq_mor := fun (X Y : Ob DepExtSet) (f g : Hom X Y) =>
    fun (x : {x : X | depExtEq (f x) (g x)}) => proj1_sig x
}.
Proof.
  cbn; intros X y f f' g g' Hf Hg.
Abort.

(* TODO: looks like DepExtSet won't have coequalizers. *)