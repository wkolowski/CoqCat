Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/".

Require Export Cat.
Require Export InitTerm.
Require Import BinProdCoprod.
(*Require Import BigProdCoprod.*)
Require Import BigProduct2.

Set Universe Polymorphism.

Instance CoqSet : Cat :=
{|
    Ob := Set;
    Hom := fun A B : Set => A -> B;
    HomSetoid := fun A B : Set =>
        {| equiv := fun f g : A -> B => forall x : A, f x = g x |};
    comp := fun (A B C : Set) (f : A -> B) (g : B -> C) (a : A) => g (f a);
    id := fun (A : Set) (a : A) => a
|}.
Proof.
  split; unfold Reflexive, Symmetric, Transitive; intros.
    (* Reflexivity *) trivial.
    (* Symmetry *) rewrite H; trivial.
    (* Transitivity *) rewrite H, H0; trivial.
  (* Composition is proper *) unfold Proper, respectful. simpl. intros.
    rewrite H0. f_equal. rewrite H. trivial.
  (* Category laws *) all:cat.
Defined.

Instance Card_Setoid : Setoid Set :=
{
    equiv := @isomorphic CoqSet (* exists f : A -> B, bijective f*)
}.
Proof. apply (isomorphic_equiv CoqSet). Defined.

Theorem CoqSet_mon_inj : forall (A B : Ob CoqSet) (f : A -> B),
    Mon f <-> @injectiveS A B {| equiv := eq |} {| equiv := eq |} f.
Proof.
  unfold Mon, injectiveS; simpl; split; intros.
    change (a = a') with ((fun _ => a) a = (fun _ => a') a).
      apply H. auto.
    apply H. apply H0.
Qed.

(*Theorem CoqSet_sec_inj : forall (A B : Set) (nonempty : A) (f : Hom A B),
    Sec f <-> injective f.
Proof.
  split; intros.
    apply CoqSet_mon_inj; [assumption | apply sec_is_mon; assumption].
    unfold Sec, injective in *.
admit.*)

Theorem CoqSet_init : @initial CoqSet Empty_set.
Proof.
  intro. exists (fun x : Empty_set => match x with end). cat.
Defined.

Theorem CoqSet_term : @terminal CoqSet unit.
Proof.
  intro. exists (fun _ => tt). cat. destruct (y x). cat.
Defined.

Instance CoqSet_has_init : has_init CoqSet :=
{
    init := Empty_set;
    create := fun (X : Set) (e : Empty_set) => match e with end
}.
Proof. cat. Defined.

Eval simpl in create CoqSet unit.

Instance CoqSet_has_term : has_term CoqSet :=
{
    term := unit;
    delete := fun (X : Set) (x : X) => tt
}.
Proof. cat. destruct (f x). cat. Defined.

Instance CoqSet_has_all_products : has_all_products CoqSet.
refine
{|
    bigProd := fun (J : Set) (A : J -> Ob CoqSet) =>
        forall j : J, A j;
    bigProj := fun (J : Set) (A : J -> Ob CoqSet) (j : J) =>
        fun (f : forall j : J, A j) => f j
|}.
Proof.
  unfold big_product; simpl; intros.
  exists (fun (x : X) (j : J) => f j x).
  cat. extensionality a. cat.
Defined.

Definition is_singleton (A : Set) : Prop :=
    exists a : A, True /\ forall (x y : A), x = y.

Theorem CoqSet_terminal_ob : forall A : Set,
    is_singleton A -> @terminal CoqSet A.
Proof.
  unfold is_singleton, terminal; intros.
  destruct H as [a [_ H]]. exists (fun _ : X => a).
  simpl; unfold unique; split; [trivial | intros].
  simpl. intros. apply H.
Restart.
  unfold is_singleton, terminal; intros.
  destruct H as [a [_ H]]. exists (fun _ : X => a). cat.
Qed.

Theorem CoqSet_prod : forall (A B : Set),
    product CoqSet (prod A B) (@fst A B) (@snd A B).
Proof.
  unfold product; intros.
  exists (fun x : X => (f x, g x)). repeat split; simpl; auto.
  intros. destruct H as [f_eq g_eq]. rewrite f_eq, g_eq.
  rewrite surjective_pairing; trivial.
Restart.
  unfold product; intros.
  exists (fun x : X => (f x, g x)). cat.
  rewrite H, H0, surjective_pairing. auto.
Qed.

Theorem CoqSet_coprod : forall (A B : Set),
    coproduct CoqSet (sum A B) (@inl A B) (@inr A B).
Proof.
  unfold coproduct; intros.
  exists (
      fun p : A + B => match p with
          | inl a => f a
          | inr b => g b
      end).
  repeat split; simpl; auto.
  intros. destruct H, x; auto.
Restart.
  unfold coproduct; intros.
  exists (
      fun p : A + B => match p with
          | inl a => f a
          | inr b => g b
      end).
  cat. destruct x; auto.
Qed.

Theorem CoqSet_ret_invertible : forall (A B : Set)
    (f : Hom A B), {g : Hom B A | g .> f = id B} ->
    invertible {| equiv := eq |} f.
Proof.
  intros. red.
    destruct H as [g H]. intro. exists (g b). simpl in *.
    change (f (g b)) with ((fun a : B => (f (g a))) b).
    change b with ((fun a : B => a) b) at 2.
    rewrite H. auto.
Qed.

Theorem CoqSet_invertible_ret : forall (A B : Set) (f : Hom A B),
    invertible {| equiv := eq |} f -> {g : Hom B A | g .> f == id B}.
Proof.
  intros. red in H.
  exists (fun b => proj1_sig (H b)). simpl.
  intro b. destruct (H b). simpl in *. auto.
Qed.

(*Theorem CoqSet_epi_sur : forall (A B : Set) (nonempty : A) (f : Hom A B),
    Epi f <-> @surjective A B {| equiv := eq |} f.
Proof.
  unfold Epi, surjective; split; intros. simpl in *.
  specialize (H A (id   
assert (H' : forall (X : Set) (g h : Hom B X),
    (forall a : A, (fun a : A => g (f a)) a = (fun a : A => h (f a)) a) ->
    forall b : B, (fun b : B => g b) b = (fun b : B => h b) b).
    intros. apply H. auto.
  
apply fn_ext_axiom. intro b.
specialize (H b). destruct H as [a H]. rewrite <- H.
unfold comp, CompSets in H0.
generalize a. rewrite <- fn_ext_axiom. assumption.
Qed.*)

Theorem CoqSet_counterexample1 :
    exists (A B C : Set) (f : Hom A B) (g : Hom B C),
    injective (f .> g) /\ ~ (injective g).
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold injective, not; simpl; split; intros.
    destruct x, y; auto.
    specialize (H true false eq_refl). discriminate H.
Qed.

Theorem CoqSet_counterexample2 : exists (A B C : Set) (f : Hom A B)
    (g : Hom B C), surjective (f .> g) /\ ~ (surjective f).
Proof.
  exists unit, bool, unit, (fun _ => true), (fun _ => tt).
  unfold surjective, not; simpl; split; intros.
    exists tt. destruct b. auto.
    destruct (H false). inversion H0.
Qed.

(* It's time to change all this shit to be constructive and proof-relevant.
Theorem CoqSet_iso_bij : forall (A B : Set) (f : Hom A B)
    (nonempty : A), Iso f -> injective f * invertible {| equiv := eq |} f.
Proof.
  unfold injective, invertible, Iso; simpl; intros. split.
    destruct H as [g [H1 H2]]. intros. rewrite <- (H1 x), <- (H1 y).
      rewrite H. auto.
    destruct H as [g [H1 H2]]. exists (g b). rewrite H2. auto.
    destruct H as [H1 H2]. exists (fun _ => nonempty). simpl.*)