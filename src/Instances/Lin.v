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
Instance Lin_Pos_product (X Y : Lin) : Pos :=
{
  pros := Lin_Pros_product X Y
}.
Proof.
  now cbn; intuition (auto with *).
Defined.

(**
  Defining product of linear orders is not possible without LEM.
*)

#[refine]
#[export]
Instance Lin_product (X Y : Lin) : Lin :=
{
  pos := Lin_Pos_product X Y;
}.
Proof.
Abort.

(**
  Coproducts of linear orders don't exist because they are kind of "connected"
  and coproducts are all about creating objects which are "disconnected".
*)

#[export]
Instance SBool : Setoid' :=
{
  carrier := bool;
  setoid := Setoid_bool;
}.

#[refine]
#[export]
Instance Pros_bool : Pros :=
{
  carrier := SBool;
  leq x y :=
    match x, y with
    | true, false => False
    | _, _ => True
    end
}.
Proof.
  - now intros [] []; cbn.
  - now intros [] []; cbn.
Defined.

#[refine]
#[export]
Instance Pos_bool : Pos :=
{
  pros := Pros_bool;
}.
Proof.
  now intros [] []; cbn.
Defined.

#[refine]
#[export]
Instance Lin_bool : Lin :=
{
  pos := Pos_bool;
}.
Proof.
  now intros [] []; cbn; auto.
Defined.

Definition SetoidHom_const_true : SetoidHom SBool SBool :=
{|
  Cat.func := fun _ => true;
|}.

Definition ProsHom_const_true : ProsHom Pros_bool Pros_bool.
Proof.
  exists SetoidHom_const_true.
  now cbn.
Defined.

Definition SetoidHom_const_false : SetoidHom SBool SBool :=
{|
  Cat.func := fun _ => false;
|}.

Definition ProsHom_const_false : ProsHom Pros_bool Pros_bool.
Proof.
  exists SetoidHom_const_false.
  now cbn.
Defined.

Lemma no_coproducts_Lin :
  HasCoproducts LinCat -> False.
Proof.
  intros [? ? ? ? H].
  destruct (H Lin_bool Lin_bool); clear H.
  destruct (leq_total (finl Lin_bool Lin_bool true) (finr Lin_bool Lin_bool true)).
  - specialize (finl_copair Lin_bool ProsHom_const_true ProsHom_const_false true);
      cbn in finl_copair.
    specialize (finr_copair Lin_bool ProsHom_const_true ProsHom_const_false true);
      cbn in finr_copair.
    change (true ≤ false).
    rewrite <- finl_copair, <- finr_copair.
    now apply func_pres_leq.
  - specialize (finl_copair Lin_bool ProsHom_const_false ProsHom_const_true true);
      cbn in finl_copair.
    specialize (finr_copair Lin_bool ProsHom_const_false ProsHom_const_true true);
      cbn in finr_copair.
    change (true ≤ false).
    rewrite <- finr_copair, <- finl_copair.
    now apply func_pres_leq.
Qed.
