Require Export Instances.Setoid.Pos.

Class Lin : Type :=
{
    pos :> Pos;
    leq_total : forall x y : pos, leq x y \/ leq y x
}.

Hint Resolve leq_total.

Coercion pos : Lin >-> Pos.

Ltac lin_simpl := pos_simpl.

Ltac linob P := try intros until P;
match type of P with
  | Lin =>
    let a := fresh P "_leq_total" in destruct P as [P a]
  | Ob _ => progress simpl in P; prosob P
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
Instance LinCat : Cat :=
{
    Ob := Lin;
    Hom := ProsHom;
    HomSetoid := @HomSetoid ProsCat;
    comp := ProsComp;
    id := ProsId
}.
Proof. 
  (* Proper *) proper. rewrite H, H0. reflexivity.
  (* Category laws *) all: lin.
Defined.

#[refine]
Instance Lin_init : Lin :=
{
    pos := Pos_init
}.
Proof. lin. Defined.

#[refine]
Instance Lin_has_init : has_init LinCat :=
{
    init := Lin_init;
    create := Pros_create
}.
Proof. lin. Defined.

#[refine]
Instance Lin_term : Lin :=
{
    pos := Pos_term
}.
Proof. lin. Defined.

#[refine]
Instance Lin_has_term : has_term LinCat :=
{
    term := Lin_term;
    delete := Pros_delete
}.
Proof. lin. Defined.

#[refine]
Instance Lin_prod_Pros (X Y : Lin) : Pros :=
{
    carrier := CoqSetoid_prodOb X Y;
    leq := fun p1 p2 : X * Y =>
      (fst p1 ≤ fst p2 /\ ~ fst p1 == fst p2) \/
      (fst p1 == fst p2 /\ snd p1 ≤ snd p2)
}.
Proof. 
  (* Proper *) proper. destruct H, H0. rewrite H, H0, H1, H2. reflexivity.
  (* Reflexivity *) lin.
  (* Transitivity *) destruct 1, 1; destruct H, H0.
    left. split; eauto. intro.
      assert (fst c == fst b); try rewrite H3 in H; eauto.
    left. split; rewrite <- H0; auto.
    left. split; rewrite H; auto.
    right. split; try rewrite H, H0; eauto. reflexivity.
Defined.

#[refine]
Instance Lin_prod_Pos (X Y : Lin) : Pos :=
{
    pros := Lin_prod_Pros X Y
}.
Proof.
  intros. destruct x, y. cbn in *. repeat
  match goal with
      | H : _ /\ _ |- _ => destruct H
      | H : _ \/ _ |- _ => destruct H
  end; intuition.
Defined.

#[refine]
Instance Lin_prod (X Y : Lin) : Lin :=
{
    pos := Lin_prod_Pos X Y
}.
Proof.
  destruct x, y; simpl.
  destruct (leq_total c c1), (leq_total c1 c),
    (leq_total c0 c2), (leq_total c2 c0); eauto.
    assert (c0 == c2) by eauto. rewrite H3.
Abort.

(* TODO : products of linear orders suck because of constructivity *)

(*Definition Lin_proj1 (X Y : Lin) : ProsHom (Lin_prod X Y) X.
Proof.
  red. exists fst. destruct 1, H; try rewrite H; lin.
Defined.

Definition Lin_proj2 (X Y : Lin) : ProsHom (Lin_prod X Y) Y.
Proof.
  red. exists snd. lin'. destruct a, a', H, H; simpl in *.
Abort. *)

(* TODO Instance Lin_has_products : has_products LinCat :=
{
    prodOb := Lin_prod;
    proj1 := Pros_proj1;
    proj2 := Pros_proj2;
    fpair := @Pros_fpair
}.
Proof.
  all: pos'; cat; try rewrite H; try rewrite H0; try destruct (y x); auto.
Defined.*)


Ltac proper_lin := proper; repeat
match goal with
    | p : _ + _ |- _ => destruct p
end;
intuition eauto;
match goal with
    | H : _ == _, H' : _ == _ |- _ =>
        rewrite <- ?H, <- ?H'; auto;
        rewrite ?H, ?H'; auto
end.

#[refine]
Instance Lin_Pros_coprod (X Y : Lin) : Pros :=
{
    carrier := CoqSetoid_coprodOb X Y;
    leq := fun p1 p2 : X + Y =>
      match p1, p2 with
        | inl x, inl x' => leq x x'
        | inr y, inr y' => leq y y'
        | inl _, inr _ => True
        | inr _, inl _ => False
      end
}.
Proof.
  proper_lin.
  all: cbn; intros; repeat
  match goal with
    | p : _ + _ |- _ => destruct p
  end; lin.
Defined.

#[refine]
Instance Lin_coprodOb (X Y : Lin) : Lin :=
{
    pos :=
    {| pros :=
      {|  carrier := CoqSetoid_coprodOb X Y;
          leq := fun p1 p2 : X + Y =>
            match p1, p2 with
              | inl x, inl x' => leq x x'
              | inr y, inr y' => leq y y'
              | inl _, inr _ => True
              | inr _, inl _ => False
            end
      |}
    |}
}.
Proof.
  proper_lin.
  all: intros; repeat
  (try match goal with
    | p : _ + _ |- _ => destruct p
  end; my_simpl; try f_equal; lin').
Defined.

Definition Lin_coproj1 (X Y : Lin) : ProsHom X (Lin_coprodOb X Y).
Proof.
  red. exists (CoqSetoid_coproj1 X Y). lin.
Defined.

Definition Lin_coproj2 (X Y : Lin) : ProsHom Y (Lin_coprodOb X Y).
Proof.
  red. exists (CoqSetoid_coproj2 X Y). lin.
Defined.

Definition Lin_copair (A B X : Lin) (f : ProsHom A X) (g : ProsHom B X)
    : ProsHom (Lin_coprodOb A B) X.
Proof.
  exists (CoqSetoid_copair f g). cbn. destruct f, g.
  destruct a, a'; intros; cbn.
    try apply l; try apply l0; auto.
    Focus 2. inversion H.
    Focus 2. apply l0. assumption.
Abort.