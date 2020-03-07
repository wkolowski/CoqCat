(** TODO: work it out.
    Remember: in a reflexive graph category, morphisms need NOT preserve
    all relations. We just have to specify which morphisms preserve
    which relations.

    Based on:
    https://www.cs.bham.ac.uk/~udr/papers/logical-relations-and-parametricity.pdf
*)

Require Import JMeq.

Lemma transport :
  forall {A : Type} (P : A -> Type) {x y : A} (p : x = y),
    P x -> P y.
Proof.
  destruct 1. intro u. exact u.
Defined.

Class ReflexiveGraphCategory : Type :=
{
    Ob  : Type;

    Mor : Ob -> Ob -> Type;

    id   : forall {X : Ob}, Mor X X;
    comp : forall {X Y Z : Ob}, Mor X Y -> Mor Y Z -> Mor X Z;

    comp_id_l : forall {X Y : Ob} (f : Mor X Y), comp id f = f;
    comp_id_r : forall {X Y : Ob} (f : Mor X Y), comp f id = f;
    comp_assoc :
      forall {A B C D : Ob} (f : Mor A B) (g : Mor B C) (h : Mor C D),
        comp (comp f g) h = comp f (comp g h);

    Rel : Ob -> Ob -> Type;

    fill :
      forall {X X' Y Y' : Ob},
        Mor X Y -> Mor X' Y' -> Rel X X' -> Rel Y Y' -> Type;

    rid :
      forall {X Y : Ob} (R : Rel X Y), fill id id R R;
    rcomp :
      forall {X X' Y Y' Z Z' : Ob}
        {f1 : Mor X Y} {f2 : Mor Y Z} {g1 : Mor X' Y'} {g2 : Mor Y' Z'}
        {R : Rel X X'} {S : Rel Y Y'} {T : Rel Z Z'},
          fill f1 g1 R S -> fill f2 g2 S T ->
            fill (comp f1 f2) (comp g1 g2) R T;

    rcomp_id_l :
      forall
        {Y Y' Z Z' : Ob}
        {f2 : Mor Y Z} {g2 : Mor Y' Z'}
        {S : Rel Y Y'} {T : Rel Z Z'}
        (iota : fill id id S S) (beta : fill f2 g2 S T),
          transport (fun p => fill p _ S T) (comp_id_l f2)
            (transport (fun p => fill _ p S T) (comp_id_l g2)
              (rcomp iota beta)) = beta;
    rcomp_rid_r :
      forall
        {X X' Y Y' : Ob}
        {f1 : Mor X Y} {g1 : Mor X' Y'}
        {R : Rel X X'} {S : Rel Y Y'}
        (alpha : fill f1 g1 R S) (iota : fill id id S S),
          JMeq (rcomp alpha iota) iota;
    rcomp_assoc :
      forall
        {A A' B B' C C' D D' : Ob}
        {f1 : Mor A B}   {g1 : Mor B C}   {h1 : Mor C D}
        {f2 : Mor A' B'} {g2 : Mor B' C'} {h2 : Mor C' D'}
        {R : Rel A A'} {S : Rel B B'} {T : Rel C C'} {Q : Rel D D'}
        (alpha : fill f1 f2 R S)
        (beta  : fill g1 g2 S T)
        (gamma : fill h1 h2 T Q),
          JMeq (rcomp (rcomp alpha beta) gamma)
               (rcomp alpha (rcomp beta gamma));

    I : forall {X : Ob}, Rel X X;

    I_fill :
      forall {X Y : Ob} (f : Mor X Y),
        fill f f I I

}.

Arguments Ob   : clear implicits.
Arguments Mor  : clear implicits.
Arguments id   : clear implicits.
Arguments comp : clear implicits.

Require Import ProofIrrelevance.

Axiom JMeq_pi :
  forall {P Q : Prop} (p : P) (q : Q), JMeq p q.

#[refine]
Instance CoqSetFunRel : ReflexiveGraphCategory :=
{
    Ob := Type;

    Mor X Y := X -> Y;
    id X := fun x : X => x;
    comp _ _ _ f g := fun x => g (f x);

    Rel X Y := X -> Y -> Prop;
    fill X X' Y Y' f g R S :=
      forall x x', R x x' -> S (f x) (g x');
    I A := eq;
}.
Proof.
  reflexivity.
  reflexivity.
  reflexivity.
  trivial.
  auto.
  cbn. intros. apply proof_irrelevance.
  cbn. intros. apply JMeq_pi.
  cbn. intros. apply JMeq_pi.
  exact f_equal. Show Proof.
Defined.

(*
Class Cat : Type :=
{
    Ob : Type;
    Hom : Ob -> Ob -> Type;

    id : forall A : Ob, Hom A A;
    comp : forall {A B C : Ob}, Hom A B -> Hom B C -> Hom A C;

    id_left : forall (A B : Ob) (f : Hom A B), comp (id A) f = f;
    id_right : forall (A B : Ob) (f : Hom A B), comp f (id B) = f;
    comp_assoc : forall {A B C D : Ob} (f : Hom A B) (g : Hom B C)
        (h : Hom C D), comp (comp f g) h = comp f (comp g h);
}.

Class ReflexiveGraphCategory : Type :=
{
    Gv     : Cat;
    Ge     : Cat;
    src    : Functor Ge Gv;
    tgt    : Functor Ge Gv;
    II     : Functor Gv Ge;
    src_II : FunctorComp II src = FunctorId Gv;
    tgt_II : FunctorComp II src = FunctorId Gv;
}.
*)
(*
Require Import Cat.Instances.Setoids.
Require Import Cat.Instances.Setoid.RelMor.

Search "Rel".

Print SetoidRelCat.
Check CoqSetoid.

Definition Gv' := CoqSetoid.
Definition Ge' := SetoidRelCat.

Definition src' : Functor Ge' Gv'.
Proof.
  esplit. Unshelve.
    Focus 4. destruct 1. cbn. exact {| setoid := setoid |}.
    Focus 4. cbn. intros [A SA] [B SB] [f H]. esplit. Unshelve.
Abort.
*)

(*
#[refine]
Instance SSet : ReflexiveGraphCategory :=
{
    Gv := CoqSetoid;
}.
Proof. Unshelve.
  esplit. Unshelve.
{
    Gv := CoqSetoid;
    Ge := SetoidRelCat;
}.
*)