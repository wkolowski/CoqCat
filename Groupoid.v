Require Export Cat.
Require Import Coq.Classes.SetoidClass.
Require Import JMeq.

Class Groupoid : Type :=
{
    cat :> Cat;
    all_iso : forall (A B : Ob cat) (f : Hom A B), Iso f
}.

Print JMeq.
Search JMeq.

Record HomGroupoid {C : Cat} (A B : Ob C) : Type :=
{
    f_ : Hom A B;
    is_iso : Iso f_
}.

Definition HomGrpd_Fun (C : Cat) (A B : Ob C) (_ : HomGroupoid A B) := f_.
Coercion HomGrpd_Fun : HomGroupoid >-> Funclass.

Instance HomGroupoid_Setoid (C : Cat) (A B : Ob C) : Setoid (HomGroupoid A B) :=
{|
    equiv := fun f g : HomGroupoid A B => f_ A B f = f_ A B g
|}.
split; trivial. split. unfold Symmetric. intros.
rewrite H. trivial.
unfold Transitive. intros. rewrite H, H0. trivial.
Defined.

Axiom eq_HomGroupoid : forall (C : Cat) (A B : Ob C) (f g : HomGroupoid A B),
    f = g <-> f_ A B f = f_ A B g.

Theorem eq_HomGrpd' : forall (C : Cat) (A B : Ob C) (f g : HomGroupoid A B),
    f = g <-> f_ A B f = f_ A B g.
split; intros.
destruct f, g. simpl. injection H. trivial.
destruct f, g. simpl in H. destruct is_iso0, is_iso1.
generalize dependent f_0. intro.
(*pattern f_0 at 1. rewrite H.*)
Abort.

(*Definition HomCatIso {C : Cat} (A B : Ob) := {f : Hom A B | Iso f}.

Definition CompCatIso : forall (C : Cat) (X Y Z : Ob) (f : HomCatIso X Y)
    (g : HomCatIso Y Z), HomCatIso X Z.
unfold HomCatIso; intros. destruct f as [f f_iso], g as [g g_iso].
exists (f .> g). apply iso_comp; assumption.
Defined.*)

Instance CatIso (C : Cat) : Cat.
simple refine
{|
    Ob := @Ob C;
    Hom := HomGroupoid
|};
simpl; intros.
destruct X as [f f_iso], X0 as [g g_iso].
exists (f .> g). apply iso_comp; assumption.
exists (id A). apply id_is_aut.
destruct f, g, h. apply eq_HomGroupoid. simpl. cat.
destruct f. apply eq_HomGroupoid. simpl. cat.
destruct f. apply eq_HomGroupoid. simpl. cat.
Defined.