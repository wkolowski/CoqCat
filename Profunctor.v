Require Import Cat.Cat.

Set Implicit Arguments.

Require Import Cat.Instances.CoqSet.
Require Import Cat.Instances.Setoids.

Require Import Cat.Contravariant.

Class Profunctor (C D E: Cat) : Type :=
{
    diob : Ob C -> Ob D -> Ob E;
    dimap : forall {X Y : Ob C} {X' Y' : Ob D},
        Hom X Y -> Hom X' Y' -> Hom (diob Y X') (diob X Y');
    dimap_Proper :> forall (X Y : Ob C) (X' Y' : Ob D),
        Proper (equiv ==> equiv ==> equiv) (@dimap X Y X' Y');
    dimap_comp : forall (X Y Z : Ob C) (X' Y' Z' : Ob D)
      (f : Hom X Y) (g : Hom Y Z) (f' : Hom X' Y') (g' : Hom Y' Z'),
        dimap (f .> g) (f' .> g') == dimap g f' .> dimap f g';
    dimap_id : forall (X : Ob C) (Y : Ob D),
        dimap (id X) (id Y) == id (diob X Y);
}.

Arguments diob [C D E Profunctor] _ _.
Arguments dimap [C D E Profunctor X Y X' Y'] _ _.

Ltac profunctor_simpl := repeat (rewrite dimap_comp || rewrite dimap_id).

Ltac profunctor := repeat
match goal with
    | |- context [Proper] => proper
    | _ => cat; try functor_simpl; profunctor_simpl; cat
end.

#[refine]
Instance HomProfunctor (C : Cat) : Profunctor C C CoqSetoid :=
{
    diob := fun X Y : Ob C =>
      {| carrier := Hom X Y; setoid := HomSetoid X Y |};
}.
Proof.
  intros ? ? ? ? f g.
    exists (fun h : Hom Y X' => f .> h .> g). proper.
  all: profunctor.
Defined.

#[refine]
Instance Const {E : Cat} (X : Ob E) (C D : Cat)
    : Profunctor C D E :=
{
    diob := fun _ _ => X;
    dimap := fun _ _ _ _ _ _ => id X
}.
Proof. all: profunctor. Defined.

#[refine]
Instance ProComp {C C' D D' E : Cat}
    (P : Profunctor C' D' E) (F : Functor C C') (G : Functor D D')
    : Profunctor C D E :=
{
    diob := fun (X : Ob C) (Y : Ob D) => diob (fob F X) (fob G Y)
}.
Proof.
  intros ? ? ? ? f g. exact (dimap (fmap F f) (fmap G g)).
  all: profunctor.
Defined.

Require Import Contravariant.

#[refine]
Instance HomFunctor (C : Cat) (X : Ob C)
    : Functor C CoqSetoid :=
{
    fob := fun Y : Ob C => {| carrier := Hom X Y; setoid := HomSetoid X Y |}
}.
Proof.
  intros A B f. exists (fun g => g .> f). proper.
  proper. all: cat.
Defined.

#[refine]
Instance HomContravariant (C : Cat) (X : Ob C)
    : Contravariant C CoqSetoid :=
{
    coob := fun Y : Ob C => {| carrier := Hom Y X; setoid := HomSetoid Y X |}
}.
Proof.
  intros Y Z f. exists (fun g => f .> g). proper.
  proper. all: cat.
Defined.

Require Import NatTrans.

Definition representable {C : Cat} (F : Functor C CoqSetoid) : Prop :=
  exists (X : Ob C) (α : NatTrans F (HomFunctor C X)),
    natural_isomorphism α.

Definition corepresentable {C : Cat} (F : Functor (Dual C) CoqSetoid) : Prop :=
  exists (X : Ob C) (α : NatTrans F (HomFunctor (Dual C) X)),
    natural_isomorphism α.

(* TODO : meditate on the definitions of (co)representability. *)