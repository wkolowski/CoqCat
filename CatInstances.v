Require Import Cat.

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
    (Mon f <-> injective f).
unfold Mon, injective in *; split; intros.
assert (H2 : (fun _ : A => a) = (fun _ => a')).
apply H. simpl. rewrite H0. trivial. 
apply const_fun in H2; [assumption | assumption].
apply fn_ext_axiom. intros. apply H. generalize a.
rewrite <- fn_ext_axiom. apply H0.
Qed.

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