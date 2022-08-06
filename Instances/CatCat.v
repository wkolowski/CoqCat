From Cat Require Import Cat.
From Cat.Limits Require Import InitTerm ProdCoprod Exponential.
From Cat.Instances Require Import Discrete FunCat.

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
Instance HasInit_CAT : HasInit CAT :=
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
Instance HasTerm_CAT : HasTerm CAT :=
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

Lemma pair_eq :
  forall {A B : Type} (a : A) (b : B) (p : A * B),
    a = fst p -> b = snd p -> (a, b) = p.
Proof.
  intros A B a b []; cbn; intros [] []; reflexivity.
Defined.

Lemma pair_eq' :
  forall {A B : Type} (x y : A * B),
    fst x = fst y -> snd x = snd y -> x = y.
Proof.
  intros A B [] []; cbn; intros [] []; reflexivity.
Defined.

#[refine]
#[export]
Instance HasProducts_CAT : HasProducts CAT :=
{
  prodOb := CAT_prodOb;
  outl := CAT_proj1;
  outr := CAT_proj2;
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
      * intros A. apply pair_eq; cbn; [apply p | apply r].
      * cbn; intros A B f.
        apply pair_eq'.
        -- rewrite <- q; clear q s.
           generalize (p A), (p B), (r A), (r B).
           destruct (fob FG A), (fob FG B); cbn.
           intros [] [] [] []; cbn; reflexivity.
        -- rewrite <- s; clear q s.
           generalize (p A), (p B), (r A), (r B).
           destruct (fob FG A), (fob FG B); cbn.
           intros [] [] [] []; cbn; reflexivity.
Defined.

Definition CoprodCatHom {C D : Cat} (X Y : Ob C + Ob D) : Type :=
match X, Y with
| inl X', inl Y' => Hom X' Y'
| inr X', inr Y' => Hom X' Y'
| _     , _      => Empty_set
end.

#[export]
Instance CoprodCatSetoid {C D : Cat} (X Y : Ob C + Ob D) : Setoid (CoprodCatHom X Y).
Proof.
  esplit. Unshelve. all: cycle 1.
  - destruct X as [X' | X'], Y as [Y' | Y']; cbn; [| destruct 1 | destruct 1 |].
    + intros f g. exact (f == g).
    + intros f g. exact (f == g).
  - destruct X as [X' | X'], Y as [Y' | Y']; cbn.
    + apply HomSetoid.
    + cat.
    + cat.
    + apply HomSetoid.
Defined.

#[refine]
#[export]
Instance CAT_coprodOb (C : Cat) (D : Cat) : Cat :=
{
  Ob := Ob C + Ob D;
  Hom := CoprodCatHom;
  HomSetoid := CoprodCatSetoid;
  id := fun A : Ob C + Ob D =>
    match A with
    | inl A' => id A'
    | inr A' => id A'
    end
}.
Proof.
  - intros [X | X] [Y | Y] [Z | Z].
    1, 8: exact comp.
    1-6: cat.
  - intros [X | X] [Y | Y] [Z | Z]; cat.
  - intros [X | X] [Y | Y] [Z | Z] [W | W]; cat.
  - intros [X | X] [Y | Y]; cat.
  - intros [X | X] [Y | Y]; cat.
Defined.

#[refine]
#[export]
Instance CAT_coproj1 (X Y : Cat) : Functor X (CAT_coprodOb X Y) :=
{
  fob := inl;
  fmap := fun _ _ f => f
}.
Proof. all: cat. Defined.

#[refine]
#[export]
Instance CAT_coproj2 (X Y : Cat) : Functor Y (CAT_coprodOb X Y) :=
{
  fob := inr;
  fmap := fun _ _ f => f
}.
Proof. all: cat. Defined.

#[refine]
#[export]
Instance CAT_copair
  (C D E : Cat) (F : Functor C E) (G : Functor D E) : Functor (CAT_coprodOb C D) E :=
{
  fob := fun X : Ob C + Ob D =>
    match X with
    | inl X' => fob F X'
    | inr X' => fob G X'
    end
}.
Proof.
  - intros [A | A] [B | B] f; cbn in *.
    + exact (fmap F f).
    + destruct f.
    + destruct f.
    + exact (fmap G f).
  - intros [A | A] [B | B] f g Heq; cbn in *; proper; cat.
  - intros [X | X] [Y | Y] [Z | Z] f g; cbn in *; proper; cat; functor.
  - intros [X | X]; cbn in *; proper; cat; functor.
Defined.

#[refine]
#[export]
Instance HasCoproducts_CAT : HasCoproducts CAT :=
{
  coprodOb := CAT_coprodOb;
  coproj1 := CAT_coproj1;
  coproj2 := CAT_coproj2;
  copair := CAT_copair
}.
Proof.
  - cbn; intros C D E F G [p q] H I [r s].
    esplit. Unshelve. all: cycle 1.
    + intros [A | A]; cbn.
      * destruct (p A). reflexivity.
      * destruct (r A). reflexivity.
    + intros [X | X] [Y | Y] f; cbn in *.
      * rewrite <- q; clear q. destruct (p X), (p Y); cbn. reflexivity.
      * contradiction.
      * contradiction.
      * rewrite <- s; clear s. destruct (r X), (r Y); cbn. reflexivity.
  - intros C D E F G; repeat split; cbn in *.
    + exists (fun _ => eq_refl); cbn. reflexivity.
    + exists (fun _ => eq_refl); cbn. reflexivity.
    + intros FG [[p q] [r s]].
      esplit. Unshelve. all: cycle 1.
      * intros [X | X]; [apply p | apply r].
      * intros [X | X] [Y | Y] f; cbn in *.
        -- rewrite <- q. reflexivity.
        -- contradiction.
        -- contradiction.
        -- rewrite <- s. reflexivity.
Defined.

#[refine]
#[export]
Instance HasExponentials_CAT : HasExponentials CAT :=
{
  expOb := @FunCat;
}.
Proof.
  - cbn; intros C D. esplit with (fob := fun '(F, X) => fob F X). Unshelve. all: cycle 3.
    + cbn. intros [F X] [G Y] [f g]; cbn in *.
      exact (component f X .> fmap G g).
    + intros [F X] [G Y] [α f] [β g] [H1 H2]; cbn in *.
      rewrite H1, H2. reflexivity.
    + intros [F X] [G Y] [H Z] [[α H1] f] [[β H2] g]; cbn in *.
      cat. rewrite H2, fmap_comp, !comp_assoc, <- H2. reflexivity.
    + intros [F X]; cbn. functor.
  - cbn; intros D E C. intros [fob fmap prp pcmp pid].
    esplit. Unshelve. all: cycle 3; cbn in *.
    + intro X. esplit with (fob := fun d => fob (X, d)).
Abort.