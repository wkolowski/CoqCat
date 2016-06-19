Add LoadPath "/home/Zeimer/Code/Coq/Cat".

Require Import ProofIrrelevance.

Require Import CatInstances.
Require Import InitTerm.
Require Import BinProdCoprod.

Axiom fn_ext_type : forall {A B : Type} (f g : A -> B),
f = g <-> forall a : A, f a = g a.

Lemma const_fun : forall (A B : Set) (nonempty : A) (b b' : B),
    b = b' <-> (fun _ : A => b) = (fun _ : A => b').
split; intros. rewrite H; trivial.
rewrite fn_ext_type in H. apply H. assumption.
Qed.

Instance HomCoqType : @CatHom Type.
split. exact (fun A B : Type => A -> B).
Defined.

Instance CompCoqType : @CatComp Type HomCoqType.
split; exact (fun (A B C : Type) (f : Hom A B) (g : Hom B C) => fun a : A => g (f a)).
Defined.

Instance IdCoqType : @CatId Type HomCoqType.
split; exact (fun (A : Type) (a : A) => a).
Defined.

Instance CatCoqType : Cat Type HomCoqType CompCoqType IdCoqType.
split; trivial.
Defined.

Instance HomCoqSet : @CatHom Set.
split. exact (fun A B : Set => A -> B).
Defined.

Instance CompCoqSet : @CatComp Set HomCoqSet.
split. exact (fun A B C : Set => fun (f : Hom A B) (g : Hom B C) =>
    fun a : A => g (f a)).
Defined.

Instance IdCoqSet : @CatId Set HomCoqSet.
split. exact (fun A : Set => fun a : A => a).
Defined.

Instance CatCoqSet : Cat Set HomCoqSet CompCoqSet IdCoqSet.
split; trivial.
Defined.

Instance HomProp : @CatHom Prop.
split. exact(fun A B : Prop => A -> B).
Defined.

Instance CompProp : @CatComp Prop HomProp.
split. exact (fun A B C : Prop => fun (f : A -> B) (g : B -> C) =>
    fun a : A => g (f a)).
Defined.

Instance IdProp : @CatId Prop HomProp.
split. exact (fun A : Prop => fun a : A => a).
Defined.

Instance Props : Cat Prop HomProp CompProp IdProp.
split; trivial.
Defined.

Theorem CoqSet_mon_inj : forall (A B : Set) (nonempty : A) (f : Hom A B),
    Mon f <-> injective f.
unfold Mon, injective; split; intros.
assert (H2 : (fun _ : A => a) = (fun _ => a')).
apply H. simpl. rewrite H0. trivial. 
apply const_fun in H2; [assumption | assumption].
apply fn_ext_type. intros. apply H. generalize a.
rewrite <- fn_ext_type. apply H0.
Qed.

(*Theorem CoqSet_sec_inj : forall (A B : Set) (nonempty : A) (f : Hom A B),
    Sec f <-> injective f.
split; intros.
apply Sets_mon_inj; [assumption | apply sec_is_mon; assumption].
unfold Sec, injective in *.
admit.*)

Theorem CoqSet_prod : forall (A B : Set),
    is_product (prod A B) (@fst A B) (@snd A B).
unfold is_product; intros.
exists (fun x : X => (f x, g x)). split; simpl.
split; rewrite fn_ext_type; trivial.
intros. destruct H as [f_eq g_eq].
rewrite f_eq, g_eq, fn_ext_type; intro; simpl.
rewrite surjective_pairing; trivial.
Qed.

Theorem CoqSet_coprod : forall (A B : Set),
    is_coproduct (sum A B) (@inl A B) (@inr A B).
unfold is_coproduct; intros.
exists (
    fun p : A + B => match p with
        | inl a => f a
        | inr b => g b
    end).
split; simpl.
split; rewrite fn_ext_type; trivial.
intros. destruct H as [f_eq g_eq].
rewrite f_eq, g_eq, fn_ext_type; intro.
destruct a; trivial.
Qed.


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

(*  Most likely there's no initial object in the category Sets, because there are
    no functions from the empty set to itself. *)

Definition is_singleton (A : Set) : Prop :=
    exists a : A, True /\ forall (x y : A), x = y.

(* Beware: requires function extensionality. *)
Theorem CoqSet_terminal_ob : forall A : Set,
    is_singleton A -> terminal_object A.
unfold is_singleton, terminal_object; intros.
destruct H as [a [_ H]]. exists (fun _ : X => a).
simpl; unfold unique; split; [trivial | intros].
rewrite fn_ext_type. intros. apply H.
Qed.

