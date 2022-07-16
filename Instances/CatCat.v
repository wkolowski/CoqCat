From Cat Require Import Cat.
From Cat.Limits Require Import InitTerm ProdCoprod.
From Cat.Instances Require Import Discrete DepExtSet.

Set Implicit Arguments.

#[export]
Instance CAT_init : Cat := Discrete Empty_set.

#[refine]
#[export]
Instance CAT_create (X : Cat) : Functor CAT_init X :=
{
  fob := fun e => match e with end;
  fmap := fun e _ _ => match e with end
}.
Proof. all: cat. Defined.

#[refine]
#[export]
Instance CAT_HasInit : HasInit CAT :=
{
  init := CAT_init;
  create := CAT_create
}.
Proof.
  cbn; intros X F.
  exists (fun e : Empty_set => match e with end).
  destruct A.
Defined.

#[export]
Instance CAT_term : Cat := Discrete unit.

#[refine]
#[export]
Instance CAT_delete (X : Cat) : Functor X CAT_term :=
{
  fob := fun _ => tt;
}.
Proof. all: cat. Defined.

#[refine]
#[export]
Instance CAT_HasTerm : HasTerm CAT :=
{
  term := CAT_term;
  delete := CAT_delete;
}.
Proof.
  cbn; intros X F.
  esplit. Unshelve. all: cycle 1.
  - intros A. destruct (fob F A). reflexivity.
  - cbn; intros A B f.
    setoid_rewrite Eqdep_dec.UIP_refl_unit.
    reflexivity.
Defined.

#[refine]
#[export]
Instance CAT_proj1 (X Y : Cat) : Functor (CAT_prodOb X Y) X :=
{
  fob := fst;
  fmap := fun _ _ => fst
}.
Proof. all: cat. Defined.

#[refine]
#[export]
Instance CAT_proj2 (X Y : Cat) : Functor (CAT_prodOb X Y) Y :=
{
  fob := snd;
  fmap := fun _ _ => snd
}.
Proof. all: cat. Defined.

#[refine]
#[export]
Instance CAT_fpair
  (X Y A : Cat) (F : Functor A X) (G : Functor A Y) : Functor A (CAT_prodOb X Y) :=
{
  fob := fun X : Ob A => (fob F X, fob G X);
  fmap := fun _ _ f => (fmap F f, fmap G f)
}.
Proof. all: cat; functor. Defined.

#[refine]
#[export]
Instance CAT_HasProducts : HasProducts CAT :=
{
  prodOb := CAT_prodOb;
  proj1 := CAT_proj1;
  proj2 := CAT_proj2;
  fpair := CAT_fpair
}.
Proof.
  - cbn; intros C D E F G [p q] H I [r s].
    esplit. Unshelve. all: cycle 1.
    + intros A. cbn. destruct (p A), (r A). reflexivity.
    + cbn; intros A B f.
      rewrite <- q, <- s; clear q s.
      destruct (p A), (p B), (r A), (r B); cbn.
      reflexivity.
  - intros C D X F G; repeat split; cbn.
    + exists (fun _ => eq_refl); cbn. reflexivity.
    + exists (fun _ => eq_refl); cbn. reflexivity.
    + intros FG [[p q] [r s]].
      esplit. Unshelve. all: cycle 1.
(*       * intros A. destruct (eq_sym (p A)), (eq_sym (r A)). symmetry. apply surjective_pairing. *)
      * intros A. rewrite p, r. symmetry. apply surjective_pairing.
      * cbn; intros A B f.
        specialize (q _ _ f); specialize (s _ _ f).
        destruct (fmap FG f). cbn in *.
        rewrite <- q, <- s; clear q s. unfold eq_ind_r. cbn.

Abort.