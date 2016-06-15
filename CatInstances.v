Require Export InitTerm.

(*Definition injective {A B : Type} (f : A -> B) : Prop := forall (a a' : A),
    f a = f a' -> a = a'.*)

(*Lemma lolz : forall (A B : Type) (f g : A -> B),
    f = g -> (forall a : A, f a = g a).
intros. rewrite H. trivial.
Qed.

Lemma fn_ext : forall (A B : Set) (f g : A -> B),
f = g -> forall a : A, f a = g a.
intros. rewrite H. trivial.
Qed.*)

Axiom fn_ext_axiom : forall {A B : Set} (f g : A -> B),
f = g <-> forall a : A, f a = g a.

Definition fn_ext : Prop := forall (A B : Type) (f g : A -> A),
    f = g <-> forall a : A, f a = g a.

Lemma const_fun : forall (A B : Set) (nonempty : A) (b b' : B),
    b = b' <-> (fun _ : A => b) = (fun _ : A => b').
split; intros. rewrite H; trivial.
rewrite fn_ext_axiom in H. apply H. assumption.
Qed.

Instance HomCoq : @CatHom Type.
split. exact (fun A B : Type => A -> B).
Defined.

Instance CompCoq : @CatComp Type HomCoq.
split; exact (fun (A B C : Type) (f : Hom A B) (g : Hom B C) => fun a : A => g (f a)).
Defined.

Instance IdCoq : @CatId Type HomCoq.
split; exact (fun (A : Type) (a : A) => a).
Defined.

Instance Coq : Cat Type HomCoq CompCoq IdCoq.
split; trivial.
Defined.

Instance HomSets : @CatHom Set.
split. exact (fun A B : Set => A -> B).
Defined.

Instance CompSets : @CatComp Set HomSets.
split. exact (fun A B C : Set => fun (f : Hom A B) (g : Hom B C) =>
    fun a : A => g (f a)).
Defined.

Instance IdSets : @CatId Set HomSets.
split. exact (fun A : Set => fun a : A => a).
Defined.

Instance Sets : Cat Set HomSets CompSets IdSets.
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

Theorem Sets_mon_inj : forall (A B : Set) (nonempty : A) (f : Hom A B),
    Mon f <-> injective f.
unfold Mon, injective in *; split; intros.
assert (H2 : (fun _ : A => a) = (fun _ => a')).
apply H. simpl. rewrite H0. trivial. 
apply const_fun in H2; [assumption | assumption].
apply fn_ext_axiom. intros. apply H. generalize a.
rewrite <- fn_ext_axiom. apply H0.
Qed.

(*Theorem Sets_epi_ret : forall (A B : Set) (f : Hom A B),
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

Theorem Sets_counterexample1 : exists (A B C : Set) (f : Hom A B) (g : Hom B C),
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

Theorem Sets_counterexample2 : exists (A B C : Set) (f : Hom A B) (g : Hom B C),
    surjective (f .> g) /\ ~ (surjective f).
exists unit, bool, unit.
exists (fun _ => true). exists (fun _ => tt).
split. simpl. unfold surjective. intro. exists tt.
destruct b. trivial.
unfold not, surjective. intro.
specialize (H false). inversion H.
discriminate H0.
Qed.

(*Theorem Sets_iso_bij : forall (A B : Set) (f : Hom A B)
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
Theorem terminal_object_Sets : forall A : Set,
    is_singleton A -> terminal_object A.
unfold is_singleton, terminal_object; intros.
destruct H as [a [_ H]]. exists (fun _ : X => a).
simpl; unfold unique; split; [trivial | intros].
rewrite fn_ext_axiom. intros. apply H.
Qed.

(* How to formulate this?
Theorem discr_is_thin : forall (A : Set) (C : @Discrete A), 5 = 5. *)

Inductive hom_disc (A : Set) : A -> A -> Prop :=
    | hom_singl : forall a : A, hom_disc A a a.

Instance HomDiscrete (A : Set) : @CatHom A.
split. exact (fun a b : A => a = b).
Defined.

Instance HomDiscrete2 (A : Set) : @CatHom A.
split. exact (hom_disc A).
Defined.

Instance CompDiscrete (A : Set) : @CatComp A (@HomDiscrete A).
split. intros a b c f g; unfold Hom, HomDiscrete.
inversion f. inversion g. trivial.
Defined.

Instance CompDiscrete2 (A : Set) : @CatComp A (@HomDiscrete2 A).
split. intros a b c f g; unfold Hom, HomDiscrete2 in *.
inversion f. inversion g. exact (hom_singl A c).
Defined.

Instance IdDiscrete (A : Set) : @CatId A (@HomDiscrete A).
split. intros a. unfold Hom, HomDiscrete. trivial.
Defined.

Instance IdDiscrete2 (A : Set) : @CatId A (@HomDiscrete2 A).
split. intro a. unfold Hom, HomDiscrete2. constructor.
Defined.

Instance Discrete (A : Set) :
    Cat A (HomDiscrete A) (CompDiscrete A) (IdDiscrete A).
split; unfold Hom, HomDiscrete in *.
intros a b c d f g h. rewrite f, g, h; trivial.
intros a b f. rewrite f; trivial.
intros. rewrite f; trivial.
Defined.

(*  BIG, REALLY BIG BEWARE: the dual category instance somehow breaks
    projection definitions in Functor and FunctorAlt. *)
Instance DualHom `(C : Cat) : @CatHom Ob.
split. destruct catHom as [Hom]. exact (fun A B : Ob => Hom B A).
Defined.

Instance DualComp `(cat : Cat) : @CatComp Ob (DualHom cat).
split. intros. destruct cat, catHom, catComp. simpl in *.
exact (comp C B A X0 X).
Defined.

Instance DualId `(C : Cat) : @CatId Ob (DualHom C).
split. intros. destruct C, catHom, catId. simpl in *.
exact (id A).
Defined.

Instance Dual `(C : Cat) : @Cat Ob (DualHom C) (DualComp C) (DualId C).
split; destruct C, catHom, catComp, catId; simpl in *; cat.
Defined.

