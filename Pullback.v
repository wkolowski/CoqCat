Require Export Cat.

Definition pullback `{C : Cat} {A B X : Ob} (f : Hom A X) (g : Hom B X)
    (P : Ob) (pA : Hom P A) (pB : Hom P B) := forall (Q : Ob) (qA : Hom Q A)
        (qB : Hom Q B), exists! u : Hom Q P, qA = u .> pA /\ qB = u .> pB.

Theorem pullback_iso_unique : forall `(C : Cat) (A B X P Q : Ob)
    (f : Hom A X) (g : Hom B X) (pA : Hom P A) (pB : Hom P B) (qA : Hom Q A)
    (qB : Hom Q B), pullback f g P pA pB -> pullback f g Q qA qB -> P ~ Q.
unfold pullback, isomorphic, Iso; intros.
destruct (H0 P pA pB) as [u1 [[u1_eq1 u1_eq2] uniq1]].
destruct (H Q qA qB) as [u2 [[u2_eq1 u2_eq2] uniq2]].
exists u1, u2. split.
destruct (H P pA pB) as (i, [[i_iso1 i_iso2] uq]).
assert (i_is_id : i = id P). apply uq. cat.
rewrite <- i_is_id.
symmetry. apply uq. split.
cat. rewrite <- u2_eq1. assumption.
cat. rewrite <- u2_eq2. assumption.
destruct (H0 Q qA qB) as (i, [[i_iso1 i_iso2] uq]).
assert (i_is_id : i = id Q). apply uq. cat.
rewrite <- i_is_id.
symmetry. apply uq. split.
cat. rewrite <- u1_eq1. assumption.
cat. rewrite <- u1_eq2. assumption.
Qed.