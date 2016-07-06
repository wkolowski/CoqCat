Require Export Cat.

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
cat2. cat2. cat2.
Defined.