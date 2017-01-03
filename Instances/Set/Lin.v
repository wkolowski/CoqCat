Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat".

Require Export Instances.Set.Pos.

Class Lin : Type :=
{
    pos : Pos;
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

Instance LinCat : Cat :=
{
    Ob := Lin;
    Hom := ProsHom;
    HomSetoid := @HomSetoid ProsCat;
    comp := ProsComp;
    id := ProsId
}.
Proof.
  (* Proper *) intros. apply (@comp_Proper ProsCat).
  (* Category laws *) all: lin.
Defined.

Instance Lin_init : Lin :=
{
    pos := Pos_init
}.
Proof. lin. Defined.

Instance Lin_has_init : has_init LinCat :=
{
    init := Lin_init;
    create := Pros_create
}.
Proof. lin. Defined.

Instance Lin_term : Lin :=
{
    pos := Pos_term
}.
Proof. lin. Defined.

Instance Lin_has_term : has_term LinCat :=
{
    term := Lin_term;
    delete := Pros_delete
}.
Proof. lin. Defined.

Instance Lin_prod (X Y : Lin) : Pros :=
{
    carrier := X * Y;
    leq := fun p1 p2 : X * Y =>
      (fst p1 ≤ fst p2 /\ fst p1 <> fst p2) \/
      (fst p1 = fst p2 /\ snd p1 ≤ snd p2)
}.
Proof.
  (* Reflxivity *) lin.
  (* Transitivity *) destruct 1, 1; destruct H, H0.
    left. split; eauto. intro.
      assert (fst c = fst b); try rewrite H3 in H; eauto.
    left. split; rewrite <- H0; auto.
    left. split; rewrite H; auto.
    right. split; try rewrite H, H0; eauto.
Defined.

Definition Lin_proj1 (X Y : Lin) : ProsHom (Lin_prod X Y) X.
Proof.
  red. exists fst. destruct 1, H; try rewrite H; lin.
Defined.

(* TODO: do linear orders even have a product? *)
Definition Lin_proj2 (X Y : Lin) : ProsHom (Lin_prod X Y) Y.
Proof.
  red. exists snd. lin'. destruct a, a', H, H; simpl in *.
Abort.

(*
Definition Lin_proj2 (X Y : Lin) : Lin_prod X Y -> Y.
Proof.
  simpl. lin'. destruct X0 as [x y].
  destruct (X_leq_total 
Defined.
*)
(*Instance Lin_has_products : has_products LinCat :=
{
    prodOb := Lin_prod;
    proj1 := Pros_proj1;
    proj2 := Pros_proj2;
    diag := @Pros_diag
}.
Proof.
  all: pos'; cat; try rewrite H; try rewrite H0; try destruct (y x); auto.
Defined.*)

Instance Lin_Pros_coprod (X Y : Lin) : Pros :=
{
    carrier := X + Y;
    leq := fun p1 p2 : X + Y =>
      match p1, p2 with
        | inl x, inl x' => leq x x'
        | inr y, inr y' => leq y y'
        | inl _, inr _ => True
        | inr _, inl _ => False
      end
}.
Proof.
  all: intros; repeat
  match goal with
    | p : _ + _ |- _ => destruct p
  end; lin.
Defined.

Instance Lin_coprodOb (X Y : Lin) : Lin :=
{
    pos :=
    {| pros :=
      {|  carrier := X + Y;
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
  all: intros; repeat
  (try match goal with
    | p : _ + _ |- _ => destruct p
  end; my_simpl; try f_equal; lin').
Defined.

Definition Lin_coproj1 (X Y : Lin) : ProsHom X (Lin_coprodOb X Y).
Proof.
  red. exists inl. lin.
Defined.

Definition Lin_coproj2 (X Y : Lin) : ProsHom Y (Lin_coprodOb X Y).
Proof.
  red. exists inr. lin.
Defined.

Definition Lin_codiag (A B X : Lin) (f : ProsHom A X) (g : ProsHom B X)
    : ProsHom (Lin_coprodOb A B) X.
Proof.
  red; simpl. exists (fun p : A + B =>
    match p with
      | inl a => f a
      | inr b => g b
    end).
  intros. destruct a.
  destruct a, a'; intros; lin. simpl. red.