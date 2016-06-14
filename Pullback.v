Require Export Cat.

Definition pullback `(C : Cat) {A B X : Ob} {f : Hom A X} {g : Hom B X}
    (P : Ob) (pA : Hom P A) (pB : Hom P B) := forall (Q : Ob) (qA : Hom Q A)
        (qB : Hom Q B), exists! u : Hom Q P, qA = u .> pA /\ qB = u .> pB.