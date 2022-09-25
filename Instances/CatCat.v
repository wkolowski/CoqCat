From Cat Require Import Cat.
From Cat.Universal Require Import Initial Terminal Product Coproduct Exponential.
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
Proof.
  all: easy.
Defined.

#[refine]
#[export]
Instance HasInit_CAT : HasInit CAT :=
{
  init := CAT_init;
  create := CAT_create
}.
Proof.
  intros X F G; cbn in *.
  now exists (fun e : Empty_set => match e with end).
Defined.

#[export]
Instance HasStrictInit_CAT : HasStrictInit CAT.
Proof.
  intros C F.
  exists (create C); split; cycle 1.
  - apply equiv_initial.
  - esplit. Unshelve. all: cbn in *; cycle 1.
    + now intros A; destruct (fob F A).
    + now intros A B G; cbn; destruct (fob F A).
Defined.

#[export]
Instance CAT_term : Cat := Discrete unit.

#[refine]
#[export]
Instance CAT_delete (X : Cat) : Functor X CAT_term :=
{
  fob := fun _ => tt;
}.
Proof.
  all: easy.
Defined.

#[refine]
#[export]
Instance HasTerm_CAT : HasTerm CAT :=
{
  term := CAT_term;
  delete := CAT_delete;
}.
Proof.
  cbn; intros X F G.
  assert (Heq : forall H : Hom X CAT_term, H == CAT_delete X).
  {
    intros H.
    esplit. Unshelve. all: cycle 1.
    - now cbn; intros A; destruct (fob H A).
    - now cbn; intros A B f; apply Eqdep_dec.UIP_refl_unit.
  }
  now rewrite (Heq F), (Heq G).
Defined.

#[refine]
#[export]
Instance CAT_outl (X Y : Cat) : Functor (CAT_product X Y) X :=
{
  fob := fst;
  fmap := fun _ _ => fst
}.
Proof.
  - now proper.
  - easy.
  - easy.
Defined.

#[refine]
#[export]
Instance CAT_outr (X Y : Cat) : Functor (CAT_product X Y) Y :=
{
  fob := snd;
  fmap := fun _ _ => snd
}.
Proof.
  - now proper.
  - easy.
  - easy.
Defined.

#[refine]
#[export]
Instance CAT_fpair
  (X Y A : Cat) (F : Functor A X) (G : Functor A Y) : Functor A (CAT_product X Y) :=
{
  fob := fun X : Ob A => (fob F X, fob G X);
  fmap := fun _ _ f => (fmap F f, fmap G f)
}.
Proof.
  - now proper.
  - now cbn; intros; rewrite !fmap_comp.
  - now cbn; intros; rewrite !fmap_id.
Defined.

Lemma CAT_fpair_unique :
  forall (X C D : Cat) (F : @Hom CAT X C) (G : @Hom CAT X D) (FG : @Hom CAT X (CAT_product C D)),
    F == FG .> CAT_outl C D -> G == FG .> CAT_outr C D -> CAT_fpair F G == FG.
Proof.
  intros X C D F G FG [p q] [r s].
  esplit. Unshelve. all: cycle 1; cbn in *; intros.
  - apply prod_eq_intro; cbn; [apply p | apply r].
  - apply prod_eq_intro.
    + rewrite <- q; clear q s.
      generalize (p A), (p B), (r A), (r B).
      destruct (fob FG A), (fob FG B); cbn.
      now intros [] [] [] []; cbn.
    + rewrite <- s; clear q s.
      generalize (p A), (p B), (r A), (r B).
      destruct (fob FG A), (fob FG B); cbn.
      now intros [] [] [] []; cbn.
Qed.

#[refine]
#[export]
Instance HasProducts_CAT : HasProducts CAT :=
{
  product := CAT_product;
  outl := CAT_outl;
  outr := CAT_outr;
  fpair := CAT_fpair
}.
Proof.
  intros C D; split; intros X F G.
  - now exists (fun _ => eq_refl); cbn.
  - now exists (fun _ => eq_refl); cbn.
  - intros Hl Hr.
    transitivity (CAT_fpair (F .> CAT_outl C D) (F .> CAT_outr C D)).
    + now symmetry; apply CAT_fpair_unique.
    + now apply CAT_fpair_unique.
Defined.

Definition CoprodCatHom {C D : Cat} (X Y : Ob C + Ob D) : Type :=
match X, Y with
| inl X', inl Y' => Hom X' Y'
| inr X', inr Y' => Hom X' Y'
| _     , _      => Empty_set
end.

#[refine]
#[export]
Instance CoprodCatSetoid {C D : Cat} (X Y : Ob C + Ob D) : Setoid (CoprodCatHom X Y) :=
{
  equiv :=
    match X, Y with
    | inl X', inl Y' => fun f g => f == g
    | inr X', inr Y' => fun f g => f == g
    | _     , _      => fun _ _ => False
    end;
}.
Proof.
  destruct X as [X' | X'], Y as [Y' | Y']; cbn.
  + now apply HomSetoid.
  + easy.
  + easy.
  + now apply HomSetoid.
Defined.

#[refine]
#[export]
Instance CAT_coproduct (C : Cat) (D : Cat) : Cat :=
{
  Ob := Ob C + Ob D;
  Hom := CoprodCatHom;
  HomSetoid := CoprodCatSetoid;
  id := fun A : Ob C + Ob D =>
    match A with
    | inl A' => id A'
    | inr A' => id A'
    end;
  comp := fun A B C =>
    match A, B, C with
    | inl A', inl B', inl C' => fun f g => f .> g
    | inr A', inr B', inr C' => fun f g => f .> g
    | _     , _     , _      => ltac:(easy)
    end;
}.
Proof.
  - now intros [X | X] [Y | Y] [Z | Z]; cbn; proper.
  - now intros [X | X] [Y | Y] [Z | Z] [W | W] *; cbn.
  - now intros [X | X] [Y | Y]; cbn.
  - now intros [X | X] [Y | Y]; cbn.
Defined.

#[refine]
#[export]
Instance CAT_finl (X Y : Cat) : Functor X (CAT_coproduct X Y) :=
{
  fob := inl;
  fmap := fun _ _ f => f
}.
Proof.
  all: easy.
Defined.

#[refine]
#[export]
Instance CAT_finr (X Y : Cat) : Functor Y (CAT_coproduct X Y) :=
{
  fob := inr;
  fmap := fun _ _ f => f
}.
Proof.
  all: easy.
Defined.

#[refine]
#[export]
Instance CAT_copair
  (C D E : Cat) (F : Functor C E) (G : Functor D E) : Functor (CAT_coproduct C D) E :=
{
  fob := fun X : Ob C + Ob D =>
    match X with
    | inl X' => fob F X'
    | inr X' => fob G X'
    end;
  fmap := fun A B =>
    match A, B with
    | inl A', inl B' => fun f => fmap F f
    | inr A', inr B' => fun f => fmap G f
    | _     , _      => ltac:(easy)
    end;
}.
Proof.
  - intros [A | A] [B | B] f g Heq; cbn; [| easy | easy |].
    + now rewrite Heq.
    + now rewrite Heq.
  - intros [X | X] [Y | Y] [Z | Z] f g; cbn in *; try easy.
    + now rewrite fmap_comp.
    + now rewrite fmap_comp.
  - now intros [X | X]; cbn in *; rewrite fmap_id.
Defined.

#[refine]
#[export]
Instance HasCoproducts_CAT : HasCoproducts CAT :=
{
  coproduct := CAT_coproduct;
  finl := CAT_finl;
  finr := CAT_finr;
  copair := CAT_copair
}.
Proof.
  intros C D; split; cbn; intros P' F G.
  - now exists (fun _ => eq_refl).
  - now exists (fun _ => eq_refl).
  - intros [p q] [r s].
    esplit. Unshelve. all: cycle 1.
    + now intros [A | A]; [apply p | apply r].
    + now intros [A | A] [B | B] H; [apply q | | | apply s].
Defined.

#[refine]
#[export]
Instance HasExponentials_CAT : HasExponentials CAT :=
{
  exponential := @FunCat;
(*   eval := fun C D =>
  {|
    fob := fun '(F, X) => fob F X;
  |}; *)
}.
Proof.
  - cbn; intros C D.
    esplit with (fob := fun '(F, X) => fob F X). Unshelve. all: cycle 3.
    + intros [F X] [G Y] [f g]; cbn in *.
      exact (component f X .> fmap G g).
    + intros [F X] [G Y] [α f] [β g] [H1 H2]; cbn in *.
      now rewrite H1, H2.
    + intros [F X] [G Y] [H Z] [[α H1] f] [[β H2] g]; cbn in *.
      now rewrite comp_assoc, H2, fmap_comp, !comp_assoc, <- H2.
    + now intros [F X]; cbn; rewrite fmap_id, comp_id_l.
  - cbn; intros D E C.
    intros [fob fmap prp pcmp pid].
    esplit. Unshelve. all: cycle 3; cbn in *.
    + intro X. esplit with (fob := fun d => fob (X, d)). Unshelve. all: cycle 3.
      * intros A B f.
Abort.