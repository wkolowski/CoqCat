Require Import ProofIrrelevance.
From Cat Require Import Instances.Setoids.

(** Alternative formalization using SProp, the universe of definitionally
    irrelevant propositions.

    Mostly copy-pasted from the other file. *)

Class ReflexiveGraphCategory : Type :=
{
  Ob  : Type;

  Mor : Ob -> Ob -> Type;

  mid   : forall {X : Ob}, Mor X X;
  mcomp : forall {X Y Z : Ob}, Mor X Y -> Mor Y Z -> Mor X Z;

  mcomp_mid_l : forall {X Y : Ob} (f : Mor X Y), mcomp mid f = f;

  mcomp_mid_r : forall {X Y : Ob} (f : Mor X Y), mcomp f mid = f;

  mcomp_assoc :
    forall {A B C D : Ob} (f : Mor A B) (g : Mor B C) (h : Mor C D),
      mcomp (mcomp f g) h = mcomp f (mcomp g h);

  Rel : Ob -> Ob -> Type;

  rid : forall {X : Ob}, Rel X X;

  fill :
    forall {X X' Y Y' : Ob},
      Mor X Y -> Mor X' Y' -> Rel X X' -> Rel Y Y' -> SProp;

  fill_mid :
    forall {X Y : Ob} (R : Rel X Y), fill mid mid R R;

  fill_rid :
    forall {X Y : Ob} (f : Mor X Y),
      fill f f rid rid;

  fcomp :
    forall {X X' Y Y' Z Z' : Ob}
      {f1 : Mor X Y} {f2 : Mor Y Z} {g1 : Mor X' Y'} {g2 : Mor Y' Z'}
      {R : Rel X X'} {S : Rel Y Y'} {T : Rel Z Z'},
        fill f1 g1 R S -> fill f2 g2 S T ->
          fill (mcomp f1 f2) (mcomp g1 g2) R T;
}.

Arguments Ob    : clear implicits.
Arguments Mor   : clear implicits.
Arguments mid   : clear implicits.
Arguments mcomp {_ X Y Z} _ _.

Inductive Box (A : Type) : SProp :=
| box : A -> Box A.

#[export] Hint Constructors Box : core.

Arguments box {A} _.

#[refine]
#[export]
Instance CoqSetFunRel : ReflexiveGraphCategory :=
{
  Ob := Type;

  Mor X Y := X -> Y;
  mid X := fun x : X => x;
  mcomp _ _ _ f g := fun x => g (f x);

  Rel X Y := X -> Y -> Prop;
  rid A := eq;

  fill X X' Y Y' f g R S :=
    Box (forall x x', R x x' -> S (f x) (g x'));
}.
Proof.
  - easy.
  - easy.
  - easy.
  - now constructor.
  - now constructor; congruence.
  - now intros * [] []; auto.
Defined.

Class SetoidRel (X Y : Setoid') : Type :=
{
  srel : X -> Y -> Type;
  srel_pres :
    forall (x1 x2 : X) (y1 y2 : Y),
      equiv x1 x2 -> equiv y1 y2 -> srel x1 y1 -> srel x2 y2;
}.

#[refine]
#[export]
Instance SetoidRelId (X : Setoid') : SetoidRel X X :=
{|
  srel := equiv;
|}.
Proof.
  now setoid.
Defined.

(* TODO *)
#[refine]
#[export]
Instance SetoidFunRel : ReflexiveGraphCategory :=
{
  Ob := Setoid';

  Mor := SetoidHom;
  mid := SetoidId;
  mcomp := SetoidComp;

  Rel := SetoidRel;
  rid := SetoidRelId;

  fill X X' Y Y' f g R S :=
    Box (forall (x : X) (x' : X'), srel x x' -> srel (f x) (g x'));
}.
Proof.
  - unfold SetoidId, SetoidComp; intros X Y []; cbn in *.
    now f_equal; apply proof_irrelevance.
  - unfold SetoidId, SetoidComp; intros X Y []; cbn in *.
    now f_equal; apply proof_irrelevance.
  - unfold SetoidId, SetoidComp; intros A B C D [] [] []; cbn in *.
    now f_equal; apply proof_irrelevance.
  - now auto.
  - now constructor; cbn; intros x x' ->.
  - now intros * [] []; constructor; cbn; auto.
Defined.