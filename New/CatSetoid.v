
Require Export Coq.Classes.SetoidClass.
Require Export JMeq.

Require Export CaseTactic.
Locate "==".

Polymorphic Class Cat : Type :=
{
    Ob : Type;
    (*Ob_Setoid : Setoid Ob;*)
    Hom : forall A B : Ob, Type;
    Hom_Setoid : forall A B : Ob, Setoid (Hom A B);
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C;
    id : forall A : Ob, Hom A A;
    comp_assoc : forall (A B C D : Ob) (f : Hom A B) (g : Hom B C) (h : Hom C D),
        comp (comp f g) h == comp f (comp g h);
    id_left : forall (A B : Ob) (f : Hom A B), comp (id A) f == f;
    id_right : forall (A B : Ob) (f : Hom A B), comp f (id B) == f
}.

Notation "f .> g" := (comp f g) (at level 50).

Ltac cat_rw := rewrite id_left || rewrite id_right || rewrite comp_assoc.
Ltac cat_rw' := rewrite id_left || rewrite id_right || rewrite <- comp_assoc.
Ltac cat_simpl := repeat cat_rw.
Ltac cat_simpl' := repeat cat_rw'.
Ltac cat := repeat (intros || cat_rw || reflexivity || auto).

Instance Setoid_TypeEq (A : Type) : Setoid A := {| equiv := eq |}.
Instance Setoid_kernel (A B : Type) (f : A -> B) : Setoid A :=
    {| equiv := fun a a' : A => f a = f a' |}.
split.
Case "Reflexivity". split.
Case "Symmetry". unfold Symmetric. intros. rewrite H. trivial.
Case "Transitivity". unfold Transitive. intros. rewrite H, H0. trivial.
Defined.

(*Program Instance CoqSet' : Cat :=
{|
    Ob := Set;
    (*Ob_Setoid := {| equiv := eq |};*)
    Hom := fun A B : Set => A -> B;
    Hom_Setoid := fun A B : Set =>
        {| equiv := fun f g : A -> B => forall x : A, f x = g x |};
    comp := fun (A B C : Set) (f : A -> B) (g : B -> C) (a : A) => g (f a);
    id := fun (A : Set) (a : A) => a
|}.
Next Obligation.
split; unfold Reflexive, Symmetric, Transitive; intros.
Case "Reflexive". trivial.
Case "Symmetric". rewrite H; trivial.
Case "Transitive". rewrite H, H0. trivial.
Defined.
*)

Instance CoqSet : Cat :=
{|
    Ob := Set;
    Hom := fun A B : Set => A -> B;
    Hom_Setoid := fun A B : Set =>
        {| equiv := fun f g : A -> B => forall x : A, f x = g x |};
    comp := fun (A B C : Set) (f : A -> B) (g : B -> C) (a : A) => g (f a);
    id := fun (A : Set) (a : A) => a
|}.
split; unfold Reflexive, Symmetric, Transitive; intros.
Case "Reflexive". trivial.
Case "Symmetric". rewrite H; trivial.
Case "Transitive". rewrite H, H0. trivial.
Case "Category laws". cat. cat. cat.
Defined.

Instance Dual (C : Cat) : Cat :=
{|
    Ob := @Ob C;
    Hom := fun A B : Ob => Hom B A;
    Hom_Setoid := fun A B : Ob => {| equiv := fun f g : Hom B A =>
        @equiv (Hom B A) (@Hom_Setoid C B A) f g |};
    comp := fun (X Y Z : Ob) (f : @Hom C Y X) (g : @Hom C Z Y) => comp g f;
    id := @id C
|}.
split; unfold Hom_Setoid, Reflexive, Symmetric, Transitive; intros.
Case "Reflexive". reflexivity.
Case "Symmetric". rewrite H; reflexivity.
Case "Transitive". rewrite H, H0. reflexivity.
Case "Category laws". cat. cat. cat.
Defined.

Theorem duality_principle : forall (P : Cat -> Prop),
    (forall C : Cat, P C) -> (forall C : Cat, P (Dual C)).
trivial.
Qed.

Class Functor (C : Cat) (D : Cat) : Type :=
{
    fob : @Ob C -> @Ob D;
    fmap : forall {A B : @Ob C}, Hom A B -> Hom (fob A) (fob B);
    pres_comp : forall {A B C : @Ob C} (f : Hom A B) (g : Hom B C),
        fmap (f .> g) = fmap f .> fmap g;
    pres_id : forall A : @Ob C, fmap (id A) = id (fob A)
}.

Ltac functor_rw := rewrite pres_comp || rewrite pres_id.
Ltac functor_rw' := rewrite <- pres_comp || rewrite <- pres_id.
Ltac functor_simpl := repeat functor_rw.
Ltac functor_simpl' := repeat functor_rw'.
Ltac functor := repeat (split || intros || functor_simpl || cat).

Instance IdFunctor (C : Cat) : Functor C C.
refine
{|
    fob := fun A : Ob => A;
    fmap := fun (A B : Ob) (f : Hom A B) => f
|};
trivial.
Defined.

Instance FunctorComp (C D E : Cat) (T : Functor C D) (S : Functor D E) : Functor C E.
refine
{|
    fob := fun A : @Ob C => fob (fob A);
    fmap := fun (A B : @Ob C) (f : Hom A B) => fmap (fmap f)
|};
functor.
Defined.

(* The term has only 93 lines, whereas in New/Functor.v, it has 1610 *)
Instance CAT : Cat :=
{|
    Ob := Cat;
    Hom := Functor;
    Hom_Setoid := fun C D : Cat => {| equiv := fun T S : Functor C D =>
        @fob C D T = @fob C D S /\ JMeq (@fmap C D T) (@fmap C D S) |};
    comp := FunctorComp;
    id := IdFunctor
|}.
split; unfold Reflexive, Symmetric, Transitive; intros.
split. trivial. trivial.
destruct H. split. rewrite H. trivial.
rewrite H0. trivial.
destruct H, H0. split. rewrite H, H0. reflexivity.
rewrite H1, H2. trivial.
simpl; cat. simpl; cat. simpl; cat.
Defined.

Print CAT.