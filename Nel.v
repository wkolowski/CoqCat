Require Import Cat.

Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | cons_nel : A -> nel A -> nel A.

Arguments singl [A] _.
Arguments cons_nel [A] _ _.

Notation "h ::: t" := (cons_nel h t) (right associativity, at level 30).

Fixpoint nel_app {A : Type} (l1 l2 : nel A) : nel A :=
match l1 with
    | singl a => cons_nel a l2
    | a ::: l1' => cons_nel a (nel_app l1' l2)
end.

Notation "l1 +++ l2" := (nel_app l1 l2) (at level 40).

Theorem app_nel_assoc : forall (A : Type) (x y z : nel A),
    x +++ (y +++ z) = (x +++ y) +++ z.
Proof.
  induction x as [h | h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Qed.

Fixpoint nel_map {A B : Type} (f : A -> B) (l : nel A) : nel B :=
match l with
    | singl x => singl (f x)
    | h ::: t => f h ::: nel_map f t
end.