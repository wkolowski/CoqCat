Require Export Cat.

Class Groupoid : Type :=
{
    cat :> Cat;
    all_iso : forall (A B : @Ob cat) (f : Hom A B), Iso f
}.
Print cat.
(*Record HomGroupoid {C : Cat} (A B : Ob) : Type :=
{
    f_ : Hom A B;
    is_iso : Iso f_
}.*)

Definition HomCatIso {C : Cat} (A B : Ob) := {f : Hom A B | Iso f}.

Definition CompCatIso : forall (C : Cat) (X Y Z : Ob) (f : HomCatIso X Y)
    (g : HomCatIso Y Z), HomCatIso X Z.
unfold HomCatIso; intros. destruct f as [f f_iso], g as [g g_iso].
exists (f .> g). apply iso_comp; assumption.
Defined.

Instance CatIso (C : Cat) : Cat.
simple refine
{|
    Ob := @Ob C;
    Hom := fun A B : Ob => {f : Hom A B | @Iso C A B f};
    (*comp := CompCatIso C
    id := _;
    comp_assoc := _;
    id_left := _;
    id_right := _*)
|};
intros.
simpl in *. destruct X as [f f_iso], X0 as [g g_iso].
exists (f .> g). apply iso_comp; assumption.
simpl. exists (id A). apply id_is_aut.
simpl in *. unfold comp. destruct f, g, h. simpl.
split.


