From Cat Require Export Instances.Pos.

Class Lin : Type :=
{
  pos :: Pos;
  leq_total : forall x y : pos, leq x y \/ leq y x
}.

#[global] Hint Resolve leq_total : core.

Coercion pos : Lin >-> Pos.

Ltac lin_simpl := pos_simpl.

Ltac linob P := try intros until P;
match type of P with
| Lin =>
  let a := fresh P "_leq_total" in destruct P as [P a]
| Ob _ => progress cbn in P; prosob P
end.

Ltac linob' P := linob P; posob' P.

Ltac linobs_template tac := intros; repeat
match goal with
| P : Lin |- _ => tac P
| P : Ob _ |- _ => tac P
end.

Ltac linobs := linobs_template linob.
Ltac linobs' := linobs_template linob'.

Ltac lin' := repeat (lin_simpl; try proshoms; try linobs'; pos).
Ltac lin := try (lin'; fail).

#[refine]
#[export]
Instance LinCat : Cat :=
{
  Ob := Lin;
  Hom := ProsHom;
  HomSetoid := @HomSetoid ProsCat;
  comp := ProsComp;
  id := ProsId
}.
Proof.
  - intros A B C f1 f2 Hf g1 g2 Hg x; cbn in *.
    now rewrite Hf, Hg.
  - now cbn.
  - now cbn.
  - now cbn.
Defined.

#[refine]
#[export]
Instance Lin_init : Lin :=
{
  pos := Pos_init
}.
Proof. easy. Defined.

#[refine]
#[export]
Instance HasInit_Lin : HasInit LinCat :=
{
  init := Lin_init;
  create := Pros_create
}.
Proof. easy. Defined.

#[export]
Instance HasStrictInit_Lin : HasStrictInit LinCat.
Proof.
  intros A [f Hf]; cbn in f.
  exists (create A); split.
  - now intros x; destruct (f x).
  - now apply equiv_initial.
Defined.

#[refine]
#[export]
Instance Lin_term : Lin :=
{
  pos := Pos_term
}.
Proof. now lin. Defined.

#[refine]
#[export]
Instance HasTerm_Lin : HasTerm LinCat :=
{
  term := Lin_term;
  delete := Pros_delete
}.
Proof. now lin. Defined.

#[refine]
#[export]
Instance Lin_Pros_product (X Y : Lin) : Pros :=
{
  carrier := SETOID_product X Y;
  leq := fun p1 p2 : X * Y =>
    fst p1 ≤ fst p2 /\ ~ fst p1 == fst p2
      \/
    fst p1 == fst p2 /\ snd p1 ≤ snd p2;
}.
Proof. 
  - intros f1 f2 [Hf1 Hf2] g1 g2 [Hg1 Hg2]; cbn in *.
    now rewrite Hf1, Hf2, Hg1, Hg2.
  - now lin.
  - cbn; intros a b c [[Hle1 Hneq1] | [Heq1 Hle1]] [[Hle2 Hneq2] | [Heq2 Hle2]].
    + left; split.
      * now eauto.
      * intros Hneq.
        assert (fst c == fst b) by now apply leq_antisym; [rewrite <- Hneq |].
        apply Hneq1.
        now rewrite Hneq, H.
    + now left; rewrite <- Heq2.
    + now left; rewrite Heq1.
    + right; split.
      * now rewrite Heq1, Heq2.
      * now eauto.
Defined.

#[refine]
#[export]
Instance Lin_product_Pos (X Y : Lin) : Pos :=
{
  pros := Lin_Pros_product X Y
}.
Proof.
  now cbn; intuition (auto with *).
Defined.

(** Defining product of linear orders is not possible without LEM and coproducts
    of linear orders don't exist because they are kind of "connected" and
    coproducts are all about creating objects which are "disconnected". *)

#[refine]
#[export]
Instance Lin_Pros_coproduct (X Y : Lin) : Pros :=
{
  carrier := SETOID_coproduct X Y;
  leq := fun p1 p2 : X + Y =>
    match p1, p2 with
    | inl x, inl x' => leq x x'
    | inr y, inr y' => leq y y'
    | inl _, inr _ => True
    | inr _, inl _ => False
    end
}.
Proof.
  - intros [a1 | b1] [a2 | b2] H12 [a3 | b3] [a4 | b4] H34; cbn in *; try easy.
    + now rewrite H12, H34.
    + now rewrite H12, H34.
  - now intros [x1 | y1] [x2 | y2] Heq; cbn in *; eauto.
  - now intros [x1 | y1] [x2 | y2] [x3 | y3] H12 H23; cbn in *; eauto.
Defined.

Lemma no_coproducts_Lin :
  HasCoproducts LinCat -> False.
Proof.
  intros [? ? ? ? _]; cbn in *.
  specialize (copair _ _ _ (finr Lin_term Lin_term) (finl Lin_term Lin_term)).
  destruct copair as [[copair Heq] Hleq]; cbn in *.
  destruct (finl Lin_term Lin_term) as [[f Hf1] Hf2]; cbn in *.
  destruct (finr Lin_term Lin_term) as [[g Hg1] Hg2]; cbn in *.
  pose (Hleq1 := Hleq (f tt) (g tt)).
  pose (Hleq2 := Hleq (g tt) (f tt)).
  destruct (leq_total (f tt) (g tt)).
  - specialize (Hleq1 H).
Abort.

(* TODO: finish products and coproducts for [Lin] *)
