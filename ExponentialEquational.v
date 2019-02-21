Require Export Cat.
Require Export InitTerm.
Require Export BinProdCoprodEquational.

(* TODO *)
Class has_exponentials (C : Cat) {hp : has_products C} : Type :=
{
    expOb : Ob C -> Ob C -> Ob C;
    eval : forall {X Y : Ob C},
      Hom (prodOb (expOb X Y) X) Y;
    curry : forall {X Y Z : Ob C},
      Hom (prodOb Z X) Y -> Hom Z (expOb X Y);
    curry_Proper :> forall X Y Z : Ob C,
      Proper (equiv ==> equiv) (@curry X Y Z);
    curry_eval :
      forall X Y : Ob C, curry eval == id (expOb X Y)
}.

(*
Theorem curry_uncurry :
  forall (C : Cat) (hp : has_products C) (he : has_exponentials C)
    (X Y Z : Ob C) (f : Hom X (expOb Y Z)),
      curry (uncurry f) == f.
Proof.
  unfold uncurry; destruct he; simpl; intros.
  do 2 red in is_exponential0.
  destruct (is_exponential0 Y Z X (f ×' id Y .> (eval0 _ _))) as [H1 H2].
  apply H2. reflexivity.
Qed.

Theorem uncurry_curry :
  forall (C : Cat) (hp : has_products C) (he : has_exponentials C)
    (X Y Z : Ob C) (f : Hom (prodOb X Y) Z),
      uncurry (curry f) == f.
Proof.
  destruct he; simpl; intros. do 2 red in is_exponential0.
  unfold uncurry. destruct (is_exponential0 Y Z X f).
  exact H.
Qed.
*)

(*
Theorem uncurry_id :
  forall (C : Cat) (hp : has_products C) (he : has_exponentials C)
    (X Y : Ob C), uncurry (id (expOb X Y)) == eval.
Proof.
  destruct he; simpl; intros.
  do 2 red in is_exponential0.
  destruct (is_exponential0 _ _ _ (eval0 X Y)) as [H1 H2].
  unfold uncurry. rewrite ProductFunctor_fmap_pres_id. cat.
Qed.
*)