Require Export Cat.

Set Universe Polymorphism.

Definition equalizer (C : Cat) {X Y : Ob C} (f g : Hom X Y)
    (E : Ob C) (e : Hom E X) : Prop :=
    setoid_unique (fun e : Hom E X => e .> f == e .> g) e.

Definition coequalizer (C : Cat) {X Y : Ob C} (f g : Hom X Y)
    (E : Ob C) (e : Hom Y E) : Prop :=
    setoid_unique (fun e : Hom Y E => f .> e == g .> e) e.

Theorem dual_equalizer_coequalizer : forall (C : Cat) (X Y E : Ob C)
    (f g : Hom X Y) (e : Hom E X),
    @equalizer C X Y f g E e <-> @coequalizer (Dual C) Y X f g E e.
Proof. unfold equalizer, coequalizer. cat. Qed.




