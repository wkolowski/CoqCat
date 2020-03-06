Require Import Cat.Cat.

Set Implicit Arguments.

Class Contravariant (C : Cat) (D : Cat) : Type :=
{
    coob : Ob C -> Ob D;
    comap : forall {X Y : Ob C}, Hom X Y -> Hom (coob Y) (coob X);
    comap_Proper :> forall X Y : Ob C,
        Proper (equiv ==> equiv) (@comap X Y);
    comap_comp : forall (X Y Z : Ob C) (f : Hom X Y) (g : Hom Y Z),
        comap (f .> g) == comap g .> comap f;
    comap_id : forall A : Ob C, comap (id A) == id (coob A)
}.

Arguments coob [C D] _ _.
Arguments comap [C D] _ [X Y] _.

#[refine]
Instance Const {D : Cat} (X : Ob D) (C : Cat)
    : Contravariant C D :=
{
    coob := fun _ => X;
    comap := fun _ _ _ => id X
}.
Proof. proper. all: cat. Defined.