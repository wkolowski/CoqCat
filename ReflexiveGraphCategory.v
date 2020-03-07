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

    mid   : forall {X : Ob}, Mor X X;
    mcomp : forall {X Y Z : Ob}, Mor X Y -> Mor Y Z -> Mor X Z;

    mcomp_id_l : forall {X Y : Ob} (f : Mor X Y), mcomp mid f = f;
    mcomp_id_r : forall {X Y : Ob} (f : Mor X Y), mcomp f mid = f;
    mcomp_assoc :
      forall {A B C D : Ob} (f : Mor A B) (g : Mor B C) (h : Mor C D),
        mcomp (mcomp f g) h = mcomp f (mcomp g h);

    Rel : Ob -> Ob -> Type;

    fill :
      forall {X X' Y Y' : Ob},
        Mor X Y -> Mor X' Y' -> Rel X X' -> Rel Y Y' -> Type;

    rid :
      forall {X Y : Ob} (R : Rel X Y), fill mid mid R R;
    rcomp :
      forall {X X' Y Y' Z Z' : Ob}
        {f1 : Mor X Y} {f2 : Mor Y Z} {g1 : Mor X' Y'} {g2 : Mor Y' Z'}
        {R : Rel X X'} {S : Rel Y Y'} {T : Rel Z Z'},
          fill f1 g1 R S -> fill f2 g2 S T ->
            fill (mcomp f1 f2) (mcomp g1 g2) R T;

    rcomp_id_l :
      forall
        {Y Y' Z Z' : Ob}
        {f2 : Mor Y Z} {g2 : Mor Y' Z'}
        {S : Rel Y Y'} {T : Rel Z Z'}
        (iota : fill mid mid S S) (beta : fill f2 g2 S T),
          transport (fun p => fill p _ S T) (mcomp_id_l f2)
            (transport (fun p => fill _ p S T) (mcomp_id_l g2)
              (rcomp iota beta)) = beta;
    rcomp_rid_r :
      forall
        {X X' Y Y' : Ob}
        {f1 : Mor X Y} {g1 : Mor X' Y'}
        {R : Rel X X'} {S : Rel Y Y'}
        (alpha : fill f1 g1 R S) (iota : fill mid mid S S),
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

Arguments Ob    : clear implicits.
Arguments Mor   : clear implicits.
Arguments mid   : clear implicits.
Arguments mcomp {_ X Y Z} _ _.

Require Import ProofIrrelevance.

Axiom JMeq_pi :
  forall {P Q : Prop} (p : P) (q : Q), JMeq p q.

#[refine]
Instance CoqSetFunRel : ReflexiveGraphCategory :=
{
    Ob := Type;

    Mor X Y := X -> Y;
    mid X := fun x : X => x;
    mcomp _ _ _ f g := fun x => g (f x);

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
  exact f_equal.
Defined.

Class Cat : Type :=
{
    Obj : Type;
    Hom : Obj -> Obj -> Type;

    id : forall A : Obj, Hom A A;
    comp : forall {A B C : Obj}, Hom A B -> Hom B C -> Hom A C;

    comp_id_l : forall (A B : Obj) (f : Hom A B), comp (id A) f = f;
    comp_id_r : forall (A B : Obj) (f : Hom A B), comp f (id B) = f;
    comp_assoc : forall {A B C D : Obj} (f : Hom A B) (g : Hom B C)
        (h : Hom C D), comp (comp f g) h = comp f (comp g h);
}.

Arguments Obj : clear implicits.
Arguments id {Cat A}.

Class Functor (C D : Cat) : Type :=
{
  fob : Obj C -> Obj D;
  fmap :
    forall {A B : Obj C}, Hom A B -> Hom (fob A) (fob B);
  pres_id :
    forall A : Obj C, fmap (@id C A) = id;
  pres_comp :
    forall (A B C0 : Obj C) (f : Hom A B) (g : Hom B C0),
      fmap (comp f g) = comp (fmap f) (fmap g);
}.

Class ReflexiveGraphCategory' : Type :=
{
    Gv     : Cat;
    Ge     : Cat;
    src    : Functor Ge Gv;
    tgt    : Functor Ge Gv;
    II     : Functor Gv Ge;
(*    src_II : FunctorComp II src = FunctorId Gv;
    tgt_II : FunctorComp II src = FunctorId Gv;*)
}.

#[refine]
Instance RGC_RGC'
  (C : ReflexiveGraphCategory) : ReflexiveGraphCategory' :=
{
    Gv :=
    {|
        Obj := Ob C;
        Hom := Mor C;
        id := mid C;
        comp := @mcomp C;
        comp_id_l := @mcomp_id_l C;
        comp_id_r := @mcomp_id_r C;
        comp_assoc := @mcomp_assoc C;
    |};

    Ge :=
    {|
        Obj := {X : Ob C & {Y : Ob C & Rel X Y}}
    |};
}.
Proof.
  idtac.
    intros (X & X' & R) (Y & Y' & S).
      exact {f : Mor C X Y & {g : Mor C X' Y' & fill f g R S}}.
    intros (X & X' & R). exists (mid C X), (mid C X'). apply rid.
    intros (X & X' & R) (Y & Y' & S) (Z & Z' & T) (f1 & f2 & F) (g1 & g2 & G).
      exists (mcomp f1 g1), (mcomp f2 g2). eapply rcomp.
        exact F.
        exact G.
    intros (X & X' & R) (Y & Y' & S) (f & g & H). admit.
    intros (X & X' & R) (Y & Y' & S) (f & g & H). admit.
    intros (A & A' & R) (B & B' & S) (Ć & Ć' & T) (D & D' & Q)
           (f1 & g1 & h1) (f2 & g2 & h2) (f3 & g3 & h3). admit.
Abort.