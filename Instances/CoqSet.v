Add LoadPath "/home/zeimer/Code/Coq/CoqCat/New".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export FunctionalExtensionality.

Set Universe Polymorphism.

Lemma const_fun : forall (A B : Set) (nonempty : A) (b b' : B),
    b = b' <-> (fun _ : A => b) = (fun _ : A => b').
Proof.
  split; intros.
    rewrite H; trivial. Print f_equal. Print functional_extensionality.
    change b with ((fun _ => b) nonempty).
    change b' with ((fun _ => b') nonempty). rewrite H. trivial.
Qed.

Instance CoqSet : Cat.
refine
{|
    Ob := Set;
    Hom := fun A B : Set => A -> B;
    comp := fun (A B C : Set) (f : A -> B) (g : B -> C) (a : A) => g (f a);
    id := fun (A : Set) (a : A) => a
|};
auto.
Defined.

Instance CoqSet_init : has_init CoqSet :=
{
  init := Empty_set
}.
Proof.
  red; simpl; intro.
  exists (fun x : Empty_set => match x with end).
  split. trivial. intros. extensionality a. inversion a.
Defined.

Instance CoqSet_term : has_term CoqSet :=
{
  term := unit
}.
Proof.
  red; simpl; intro.
  exists (fun _ => tt).
  split. trivial. intros. extensionality a. destruct (x' a). trivial.
Defined.

Eval compute in init.

Theorem no_zero : ~ exists A : Set, zero_object A.
Proof.
  destruct 1 as [A [HI HT]].
  apply (initial_ob_iso_unique CoqSet A init) in HI; auto.
  apply (terminal_ob_iso_unique CoqSet A term) in HT; auto.
  simpl in *. cut (unit ~ Empty_set). intro.
  destruct H as [f _]. simpl in *. specialize (f tt). inversion f.
  rewrite <- HT. auto.
Qed.

Definition is_singleton (A : Set) : Prop :=
    exists a : A, True /\ forall (x y : A), x = y.

(* Beware: requires function extensionality. *)
Theorem CoqSet_terminal_ob : forall A : Set,
    is_singleton A -> @terminal CoqSet A.
unfold is_singleton, terminal; intros.
destruct H as [a [_ H]]. exists (fun _ : X => a).
simpl; unfold unique; split; [trivial | intros].
extensionality arg. apply H.
Qed.

Theorem CoqSet_mon_inj : forall (A B : Set) (nonempty : A) (f : A -> B),
    Mon f <-> injective f.
Proof.
  unfold Mon, injective; split; intros.
    assert (H2 : (fun _ : A => a) = (fun _ => a')).
      apply H. simpl; rewrite H0. trivial.
      apply const_fun in H2; assumption.
    simpl in *. extensionality x. apply H.
      change (f (g x)) with ((fun a : X => f (g a)) x).
      change (f (h x)) with ((fun a : X => f (h a)) x).
      rewrite H0. trivial.
Qed.

(*Theorem CoqSet_sec_inj : forall (A B : Set) (nonempty : A) (f : Hom A B),
    Sec f <-> injective f.
split; intros.
apply Sets_mon_inj; [assumption | apply sec_is_mon; assumption].
unfold Sec, injective in *.
admit.*)

Theorem CoqSet_prod : forall (A B : Set),
    product CoqSet (prod A B) (@fst A B) (@snd A B).
Proof.
  unfold product; intros.
  exists (fun x : X => (f x, g x)). split; simpl.
    split; apply eta_expansion.
    destruct 1 as [f_eq g_eq].
      rewrite f_eq, g_eq. extensionality arg.
      rewrite surjective_pairing; trivial.
Qed.

Instance CoqSet_prod' : has_products CoqSet :=
{
  prod' := prod;
  proj1' := @fst;
  proj2' := @snd
}.
apply CoqSet_prod.
Defined.

Instance CoqSet_prod_functor : Functor (CAT_prod CoqSet) CoqSet.
refine
{|
  fob := fun A : Ob (CAT_prod CoqSet) => prod (fst A) (snd A);
  fmap := fun (A B : Ob (CAT_prod CoqSet)) (f : Hom A B) =>
    fun a : fst A * snd A => (fst f (fst a), snd f (snd a))
|};
functor; simpl. extensionality a. destruct a. trivial.
Defined.

Instance CoqSet_has_prod_functor : has_prod_functor CoqSet.
refine
{|
  prod_functor := CoqSet_prod_functor;
  proj1'' := fun A B : Set => @fst A B;
  proj2'' := fun A B : Set => @snd A B
|}.
intros. simpl. apply CoqSet_prod.
Defined.

Eval compute in prod_functor (nat, nat).

Eval compute in nat × nat. Print fmap.
Hint Unfold CAT_prod.
Hint Unfold Hom CAT_prod.
Eval compute in fob prod_functor (nat, nat).
Eval compute in fmap prod_functor (S, S).
Eval compute in @fmap (CAT_prod CoqSet) CoqSet prod_functor (S, S) (3, 4).

Theorem CoqSet_coprod : forall (A B : Set),
    coproduct CoqSet (sum A B) (@inl A B) (@inr A B).
Proof.
  unfold coproduct; intros.
  exists
    (fun p : A + B => match p with
        | inl a => f a
        | inr b => g b
    end).
  split; simpl.
    split; apply eta_expansion.
    destruct 1 as [f_eq g_eq].
      rewrite f_eq, g_eq. extensionality arg.
      destruct arg; trivial.
Qed.

Instance CoqSet_coprod' : has_coproducts CoqSet :=
{
  coprod := sum;
  coproj1 := @inl;
  coproj2 := @inr
}.
apply CoqSet_coprod.
Defined.

Eval compute in coprod nat nat.

(*Theorem CoqSet_epi_ret : forall (A B : Set) (f : Hom A B),
    Ret f <-> surjective f.
unfold Ret, surjective; split; intros.
destruct H as [g eq].
unfold comp, CompSets in *.

Focus 2.
assert (g : B -> A). intro b. specialize (H b).
destruct H. 



Theorem Sets_epi_sur : forall (A B : Set) (nonempty : A) (f : Hom A B),
    Epi f <-> surjective f.
unfold Epi, surjective; split; intros.
Print ex_intro.
unfold comp, CompSets in H.
assert (H' : forall (X : Set) (g h : Hom B X),
    (fun a : A => g (f a)) = (fun a : A => h (f a)) ->
    (fun b : B => g b) = (fun b : B => h b)).
intros. apply H. assumption.


Focus 2.
apply fn_ext_axiom. intro b.
specialize (H b). destruct H as [a H]. rewrite <- H.
unfold comp, CompSets in H0.
generalize a. rewrite <- fn_ext_axiom. assumption.
Qed.*)

Theorem CoqSet_counterexample1 : exists (A B C : Set) (f : Hom A B) (g : Hom B C),
    injective (f .> g) /\ ~ (injective g).
exists unit, bool, unit.
exists (fun _ => true). exists (fun _ => tt).
split. simpl. unfold injective; intros; trivial.
destruct a. destruct a'. trivial.
unfold not, injective. intros.
specialize (H true false).
assert (true = false). apply H. trivial.
discriminate H0.
Qed.

Theorem CoqSet_counterexample2 : exists (A B C : Set) (f : Hom A B) (g : Hom B C),
    surjective (f .> g) /\ ~ (surjective f).
exists unit, bool, unit.
exists (fun _ => true). exists (fun _ => tt).
split. simpl. unfold surjective. intro. exists tt.
destruct b. trivial.
unfold not, surjective. intro.
specialize (H false). inversion H.
discriminate H0.
Qed.

(*Theorem CoqSet_iso_bij : forall (A B : Set) (f : Hom A B)
    (nonempty : A), Iso f <-> bijective f.
(*unfold bijective, injective, surjective;*) split; intros.
split; intros. rewrite iso_iff_sec_ret in H.
destruct H as [H1 H2]. apply sec_is_mon in H1.
rewrite Sets_mon_inj in H1. assumption. assumption.
Focus 2.
rewrite iso_iff_sec_ret. split.
destruct H as [a b]. unfold injective, surjective in *.*)