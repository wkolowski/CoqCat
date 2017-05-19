Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Base.

Require Export Cat.
Require Export InitTerm.
Require Import BinProdCoprod.
Require Import BigProdCoprod.
Require Import Equalizer.
Require Import Exponential.
Require Import CartesianClosed.

Require Import Functor.

Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

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
  (* Equivalence *) solve_equiv.
  (* Composition is proper *) proper. rewrite H, H0. auto.
  (* Category laws *) all: cat.
Defined.

Theorem CoqSet_mon_inj : forall (A B : Ob CoqSet) (f : A -> B),
    Mon f <-> injective f.
Proof.
  unfold Mon, injective; simpl; split; intros.
    change (x = y) with ((fun _ => x) x = (fun _ => y) x).
      apply H. auto.
    apply H. apply H0.
Defined.

(* TODO : Theorem CoqSet_sec_inj : forall (A B : Set) (nonempty : A) (f : Hom A B),
    Sec f <-> injective f.
Proof.
  split; intros.
    apply CoqSet_mon_inj. apply sec_is_mon. assumption.
    unfold Sec, injective in *.
admit.*)

(* Looks like it doesn't hold constructively. *)
Theorem CoqSet_epi_sur : forall (A B : Set) (nonempty : A) (f : Hom A B),
    Epi f <-> surjective f.
Proof.
  unfold Epi, surjective; split; intros. simpl in *.
  Focus 2. simpl in *. intro. destruct (H x). rewrite <- H1. auto.
  specialize (H B (fun b : B => f nonempty) (fun _ => b)). simpl in H.
  exists nonempty. apply H. intro.
Abort.

Theorem CoqSet_ret_sur : forall (X Y : Set) (f : Hom X Y),
    Ret f <-> surjective f.
Proof.
  unfold Ret, surjective; simpl; split; intros.
    destruct H as [g eq]. exists (g b). apply eq.
    exists (
    fun y : Y => proj1_sig (constructive_indefinite_description _ (H y))).
      intro y. destruct (constructive_indefinite_description _ (H y)).
      simpl. assumption.
Defined.

Theorem CoqSet_iso_bij : forall (A B : Set) (f : Hom A B),
    Iso f <-> bijective f.
Proof.
  unfold bijective, injective, surjective, Iso; simpl; split; intros.
    split; intros.
      destruct H as [g [H1 H2]]. rewrite <- (H1 x), <- (H1 y).
        rewrite H0. auto.
      destruct H as [g [H1 H2]]. exists (g b). rewrite H2. auto.
Restart.
  split; intros.
    red. rewrite iso_iff_mon_ret in H. destruct H. split.
      rewrite <- CoqSet_mon_inj. assumption.
      rewrite <- CoqSet_ret_sur. assumption.
    destruct H. rewrite iso_iff_mon_ret. split.
      rewrite CoqSet_mon_inj. assumption.
      rewrite CoqSet_ret_sur. assumption.
Defined.

(* TODO : remove Theorem CoqSet_ret_invertible : forall (A B : Set)
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
Qed.*)

Instance CoqSet_has_init : has_init CoqSet :=
{
    init := Empty_set;
    create := fun (X : Set) (e : Empty_set) => match e with end
}.
Proof. cat. Defined.

Instance CoqSet_has_term : has_term CoqSet :=
{
    term := unit;
    delete := fun (X : Set) (x : X) => tt
}.
Proof. cat. Defined.

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

(* TODO : remove Theorem CoqSet_prod : forall (A B : Set),
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
Qed. *)

Definition CoqSet_fpair (X Y A : Set) (f : Hom A X) (g : Hom A Y)
    : Hom A (prod X Y) := fun x : A => (f x, g x).

Instance CoqSet_has_products : has_products CoqSet :=
{
    prodOb := prod;
    proj1 := @fst;
    proj2 := @snd;
    fpair := CoqSet_fpair
}.
Proof.
  all: unfold CoqSet_fpair.
  (* Proper *) proper. rewrite H, H0. auto.
  (* Product law *) red; cat. rewrite H, H0. destruct (y x). auto.
Defined.

(* TODO : remove Instance CoqSet_prod_functor : Functor (CAT_prod CoqSet CoqSet) CoqSet.
refine
{|
  fob := fun A : Ob (CAT_prod CoqSet CoqSet) => prod (fst A) (snd A);
  fmap := fun (A B : Ob (CAT_prod CoqSet CoqSet)) (f : Hom A B) =>
    fun a : fst A * snd A => (fst f (fst a), snd f (snd a))
|}.
Proof.
  repeat red. intros. simpl in *. destruct H. rewrite H, H0. auto.
  functor.
  functor. destruct x. auto.
Defined. *)

(* Beware! Requires functional extensionality. *)
Instance CoqSet_has_all_products : has_all_products CoqSet :=
{
    bigProdOb := fun (J : Set) (A : J -> Ob CoqSet) =>
        forall j : J, A j;
    bigProj := fun (J : Set) (A : J -> Ob CoqSet) (j : J) =>
        fun (f : forall j : J, A j) => f j;
    tuple := fun (J : Set) (A : J -> Ob CoqSet) (X : Ob CoqSet)
        (f : forall j : J, Hom X (A j)) (x : X) (j : J) => f j x
}.
Proof.
  (* Proper *) cat. extensionality j. auto.
  (* Universal property *) red; cat. extensionality a. auto.
Defined.

(* TODO : remove Theorem CoqSet_coprod : forall (A B : Set),
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
Qed. *)

(* TODO : remove Instance CoqSet_coprod_functor : Functor (CAT_prod CoqSet CoqSet) CoqSet.
refine
{|
    fob := fun X : Ob (CAT_prod CoqSet CoqSet) => sum (fst X) (snd X);
    fmap := fun (X Y : Ob (CAT_prod CoqSet CoqSet)) (f : Hom X Y) =>
        fun (x : sum (fst X) (snd X)) => match x with
            | inl x1 => inl (fst f x1)
            | inr y1 => inr (snd f y1)
        end
|}.
Proof.
  repeat red; simpl. destruct 1. destruct x0; [rewrite H| rewrite H0]; auto.
  all: simpl; destruct x; cat.
Defined. *)

Definition CoqSet_coprodOb := sum.
Definition CoqSet_coproj1 := @inl.
Definition CoqSet_coproj2 := @inr.

Definition CoqSet_copair (X Y A : Set) (f : X -> A) (g : Y -> A)
    : sum X Y -> A := fun p : X + Y =>
match p with
    | inl x => f x
    | inr y => g y
end.

Instance CoqSet_has_coproducts : has_coproducts CoqSet :=
{
    coprodOb := sum;
    coproj1 := @inl;
    coproj2 := @inr;
    copair := CoqSet_copair
}.
Proof.
  all: repeat red; cat;
  match goal with | x : _ + _ |- _ => destruct x end; cat.
Defined.

Instance CoqSet_has_all_coproducts : has_all_coproducts CoqSet :=
{
    bigCoprodOb := fun (J : Set) (A : J -> Ob CoqSet) =>
        {j : J & A j};
    bigCoproj := fun (J : Set) (A : J -> Ob CoqSet) (j : J) =>
        fun (x : A j) => existT A j x;
    cotuple := fun (J : Set) (A : J -> Ob CoqSet) (X : Ob CoqSet)
        (f : forall j : J, Hom (A j) X) (p : {j : J & A j}) =>
          f (projT1 p) (projT2 p)
}.
Proof.
  all: try red; cat.
Defined.

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

Instance CoqSet_has_equalizers : has_equalizers CoqSet :=
{
    eq_ob := fun (X Y : Ob CoqSet) (f g : Hom X Y) =>
        {x : X | f x = g x};
    eq_mor := fun (X Y : Ob CoqSet) (f g : Hom X Y) =>
        fun (x : {x : X | f x = g x}) => proj1_sig x
}.
Proof.
  unfold equalizer; simpl; split; intros.
    destruct x; simpl. auto.
    exists (fun x : E' => exist (fun x : X => f x = g x) (e' x) (H x)).
    cat. specialize (H0 x). destruct (y x). simpl in *. subst.
    f_equal. apply proof_irrelevance.
Defined.

(* Not sure if it's even true *)
(*Instance CoqSet_has_coequalizers : has_coequalizers CoqSet :=
{
    coeq_ob := fun (X Y : Ob CoqSet) (f g : Hom X Y) =>
        {T : Set & {y : Y | T = {y' : Y | exists x : X, f x = y /\ g x = y /\ y = y'}}}
    (*coeq_mor := fun (X Y : Ob CoqSet) (f g : Hom X Y) =>*)
        
}.
Proof.
  simpl; intros X Y f g y. exists {A : {y : Y | 
  unfold coequalizer; simpl; intros. cat. f_equal.
*)

Instance CoqSet_has_exponentials : has_exponentials CoqSet :=
{
    expOb := fun X Y : Set => X -> Y;
    eval := fun (X Y : Set) (fx : prodOb (X -> Y) X) => (fst fx) (snd fx);
    curry := fun (X Y Z : Set) (f : Z * X -> Y) (z : Z) =>
      fun x : X => f (z, x)
}.
Proof.
  proper. extensionality a. rewrite H. reflexivity.
  do 2 red; simpl; split; intros.
    destruct x; simpl. reflexivity.
    extensionality x'. rewrite <- H. simpl. reflexivity.
Defined.

Instance CoqSet_cartesian_closed : cartesian_closed CoqSet :=
{
    ccc_term := CoqSet_has_term;
    ccc_prod := CoqSet_has_products;
    ccc_exp := CoqSet_has_exponentials;
}.