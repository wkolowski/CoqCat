From Cat Require Import Cat.

Set Implicit Arguments.

Definition equalizer
  (C : Cat) {X Y : Ob C} (f g : Hom X Y)
  (E : Ob C) (e : Hom E X)
  (factorize : forall {E' : Ob C} {e' : Hom E' X}, e' .> f == e' .> g -> Hom E' E)
  : Prop :=
    e .> f == e .> g
      /\
    forall (E' : Ob C) (e' : Hom E' X) (H : e' .> f == e' .> g),
      setoid_unique (fun u : Hom E' E => u .> e == e') (factorize H).

Class HasEqualizers (C : Cat) : Type :=
{
  eq_ob :
    forall {X Y : Ob C}, Hom X Y -> Hom X Y -> Ob C;
  Proper_eq_ob :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' -> JMequiv (id (eq_ob f g)) (id (eq_ob f' g'));
  eq_mor :
    forall {X Y : Ob C} (f g : Hom X Y), Hom (eq_ob f g) X;
  eq_mor_ok :
    forall (X Y : Ob C) (f g : Hom X Y),
      eq_mor f g .> f == eq_mor f g .> g;
  Proper_eq_mor :
    forall (X Y : Ob C) (f f' g g' : Hom X Y),
      f == f' -> g == g' ->
        JMequiv (eq_mor f g) (eq_mor f' g');
  factorize :
    forall {X Y : Ob C} [f g : Hom X Y] [E' : Ob C] [e' : Hom E' X],
      e' .> f == e' .> g -> Hom E' (eq_ob f g);
  Proper_factorize :
    forall
      (X Y E' : Ob C) (f f' g g' : Hom X Y) (e' : Hom E' X)
      (H : e' .> f == e' .> g) (H' : e' .> f' == e' .> g'),
        f == f' -> g == g' -> JMequiv (factorize H) (factorize H');
  universal :
    forall
      {X Y : Ob C} [f g : Hom X Y]
      [E' : Ob C] [e' : Hom E' X] (H : e' .> f == e' .> g)
      (h : Hom E' (eq_ob f g)),
        factorize H == h <-> h .> eq_mor f g == e'
}.

Arguments eq_ob     [C _ X Y] _ _.
Arguments eq_mor    [C _ X Y] _ _.
Arguments factorize [C _ X Y f g E' e'] _.

Section HasEqualizers.

Context
  [C : Cat] [heq : HasEqualizers C]
  [X Y : Ob C]
  [f g : Hom X Y].

Lemma universal' :
  forall {E' : Ob C} {e' : Hom E' X} (H : e' .> f == e' .> g),
    factorize H .> eq_mor f g == e'.
Proof.
  intros.
  rewrite <- universal.
  reflexivity.
Qed.

Lemma isMono_equalizer :
  isMono (eq_mor f g).
Proof.
  intros A h1 h2 Heq.
  assert (H1 : (h1 .> eq_mor f g) .> f == (h1 .> eq_mor f g) .> g)
    by (rewrite !comp_assoc, eq_mor_ok; reflexivity).
  destruct (@universal _ _ _ _ f g _ (h1 .> eq_mor f g) H1 h1) as [_ <-]; [| reflexivity].
  destruct (@universal _ _ _ _ f g _ (h1 .> eq_mor f g) H1 h2) as [_ <-].
  - reflexivity.
  - symmetry. assumption.
Qed.

End HasEqualizers.