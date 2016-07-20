Require Export Coq.Classes.SetoidClass.
Require Export JMeq.
Print Setoid.

Polymorphic Class CatS : Type :=
{
    Ob : Type;
    Ob_Setoid : Setoid Ob;
    Mor : Type;
    Mor_Setoid : Setoid Mor;
    Hom : Ob -> Ob -> Mor;
    Hom_Proper : Proper (equiv ==> equiv ==> equiv) Hom;
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C;
    comp_Proper : forall A B C : Ob,
        Proper (equiv ==> equiv ==> equiv) (@comp A B C);
    comp_assoc : forall (A B C D : Ob) (f : Hom A B) (g : Hom B C) (h : Hom C D),
        comp (comp f g) h == comp f (comp g h);
    (*Type_Setoid : Setoid Type;
    Hom_Setoid : forall A B : Ob, Setoid (Hom A B);
    Hom_Proper : forall A B : Ob,
        Proper (equiv ==> equiv ==> equiv) Hom;
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C;
    comp_Proper : forall A B C : Ob,
        Proper (equiv ==> equiv ==> equiv) (@comp A B C);
    comp_assoc : forall (A B C D : Ob) (f : Hom A B) (g : Hom B C) (h : Hom C D),
        comp (comp f g) h == comp f (comp g h);
    id : forall A : Ob, Hom A A;
    id_Proper : Proper ((@equiv Ob Ob_Setoid) ==> equiv) id;
    id_left : forall (A B : Ob) (f : Hom A B), comp (id A) f == f;
    id_right : forall (A B : Ob) (f : Hom A B), comp f (id B) == f*)
}.

Print ObS.