Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.

Definition pullback (C : Cat) {A B X : Ob C} (f : Hom A X) (g : Hom B X)
  (P : Ob C) (pA : Hom P A) (pB : Hom P B) := forall (Q : Ob C) (qA : Hom Q A)
    (qB : Hom Q B), exists!! u : Hom Q P, qA == u .> pA /\ qB == u .> pB.

Theorem pullback_iso_unique : forall (C : Cat) (A B X P Q : Ob C)
    (f : Hom A X) (g : Hom B X) (pA : Hom P A) (pB : Hom P B) (qA : Hom Q A)
    (qB : Hom Q B), pullback C f g P pA pB -> pullback C f g Q qA qB -> P ~ Q.
Proof.
  unfold pullback, isomorphic, Iso; intros.
  destruct (H0 P pA pB) as [u1 [[u1_eq1 u1_eq2] uniq1]],
(H Q qA qB) as [u2 [[u2_eq1 u2_eq2] uniq2]].
  exists u1, u2; split.
    destruct (H P pA pB) as (i, [[i_iso1 i_iso2] uq]).
      assert (i_is_id : i == id P). apply uq; cat.
      rewrite <- i_is_id. symmetry. apply uq. split.
        cat. rewrite <- u2_eq1. assumption.
        cat. rewrite <- u2_eq2. assumption.
    destruct (H0 Q qA qB) as (i, [[i_iso1 i_iso2] uq]).
      assert (i_is_id : i == id Q). apply uq; cat.
      rewrite <- i_is_id. symmetry. apply uq. split.
        cat. rewrite <- u1_eq1. assumption.
        cat. rewrite <- u1_eq2. assumption.
Qed.

Definition pullback_skolem
  (C : Cat) {X Y A : Ob C} (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (e : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P)
  : Prop := p1 .> f == p2 .> g /\
    forall (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y),
      setoid_unique (fun u : Hom Q P => q1 .> f == q2 .> g) (e Q q1 q2).

Theorem pullback_skolem_iso_unique :
  forall (C : Cat) (X Y A : Ob C) (f : Hom X A) (g : Hom Y A)
  (P : Ob C) (p1 : Hom P X) (p2 : Hom P Y)
  (e : forall (P' : Ob C) (p1' : Hom P' X) (p2' : Hom P' Y), Hom P' P)
  (Q : Ob C) (q1 : Hom Q X) (q2 : Hom Q Y)
  (e' : forall (Q' : Ob C) (q1' : Hom Q' X) (q2' : Hom Q' Y), Hom Q' Q),
    pullback_skolem C f g P p1 p2 e ->
    pullback_skolem C f g Q q1 q2 e' ->
    P ~ Q.
Proof.
  intros. destruct H as [Heq Hpull], H0 as [Heq' Hpull'].
  red. exists (e' P p1 p2).
  red. exists (e Q q1 q2).
  split.
    destruct (Hpull P p1 p2). specialize (H0 (e' P p1 p2 .> e Q q1 q2) H).
      rewrite <- H0. destruct (Hpull P p1 p2). apply H2. assumption.
    destruct (Hpull' Q q1 q2). specialize (H0 (e Q q1 q2 .> e' P p1 p2) H).
      rewrite <- H0. destruct (Hpull' Q q1 q2). apply H2. assumption.
Qed.
    