Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Class Sgr : Type :=
{
    carrier : Type;
    op : carrier -> carrier -> carrier;
    assoc : forall x y z : carrier, op x (op y z) = op (op x y) z
}.

Coercion carrier : Sgr >-> Sortclass.

Hint Resolve assoc.

Ltac sgr_simpl :=
match goal with
  (* Associativity *)
  | H : context [?op _ (?op _ _)] |- _ => rewrite assoc in H
  | H : context [?op (?op _ _) _] |- _ => rewrite assoc in H
  | |- context [?op _ (?op _ _)] => rewrite assoc
  | |- context [?op (?op _ _) _] => rewrite assoc
  (* Homomorphisms *)
  | f : ?X -> ?Y, X_op : ?X -> ?X -> ?X, pres_op :
    forall x x' : ?X, ?f (?X_op x x') = ?Y_op (?f x) (?f x') |- _ =>
    match goal with
      | H : context [?f (?X_op _ _)] |- _ => rewrite pres_op in H
      | |- context [?f (?X_op _ _)] => rewrite pres_op
    end
  | _ => idtac
end; repeat red; simpl in *; intros.

Ltac sgrob S := try intros until S;
match type of S with
  | Sgr => 
    let a := fresh S "_op" in
    let b := fresh S "_assoc" in destruct S as [S a b]
  | Ob _ => progress simpl in S; sgrob S
end; sgr_simpl.

Ltac wut S l :=
match l with
    | nil => idtac
    | cons ?h ?t => let x := fresh S "_" h in destruct S as [x S]; wut S t
end.

Ltac sgrobs := repeat
match goal with
  | S : Sgr |- _ => sgrob S
  | S : Ob _ |- _ => sgrob S
end; sgr_simpl.

Definition SgrHom (A B : Sgr) : Type :=
    {f : A -> B | forall x y : A, f (op x y) = op (f x) (f y)}.

Definition SgrHom_Fun (A B : Sgr) (f : SgrHom A B) : A -> B := proj1_sig f.
Coercion SgrHom_Fun : SgrHom >-> Funclass.

Ltac sgrhom f := try intros until f;
match type of f with
  | SgrHom _ _ =>
      let a := fresh f "_pres_op" in destruct f as [?f a]
  | Hom _ _ => progress simpl in f; sgrhom f
end; sgr_simpl.

Ltac sgrhoms := intros; repeat
match goal with
  | f : SgrHom _ _ |- _ => sgrhom f
  | f : Hom _ _ |- _ => sgrhom f
  | _ => idtac
end; sgr_simpl.

Ltac sgr' := repeat (sgr_simpl || sgrobs || sgrhoms || cat).
Ltac sgr := try (sgr'; fail).

Require Import String.

Ltac weird l X := match l with
    | EmptyString => idtac "wut"
    | String ?h _ => let x := fresh X "_" h in destruct X as [x X]
end.

Ltac weird' l X := match l with
    | nil => idtac "wut"
    | cons ?h _ => let x := fresh X "_" h in destruct X as [x X]
end.

Ltac length' l :=
match l with
    | nil => constr:(0)
    | cons _ ?t => let n := length' t in constr:(S n)
end.

Goal False.
  let n := length' (cons 1 nil) in pose n.

Instance SgrHomSetoid (X Y : Sgr) : Setoid (SgrHom X Y) :=
{
    equiv := fun f g : SgrHom X Y => forall x : X, f x = g x
}.
Proof.

(*pose (l := cons 1 (cons 5 nil)).

let n := length' (cons 1 (cons 5 nil)) in pose n.
Print string.
weird EmptyString X. 
Example stringEx : string := "This is a string".
(* TODO *)  let x := fresh X "_" "1" in destruct X as [x X].
weird' (cons stringEx nil) X.

Check cons (String "dupa") nil.
weird (String "a" EmptyString) X.


pose (y := weird l).*)

 solve_equiv. Defined.

Definition SgrComp (A B C : Sgr) (f : SgrHom A B) (g : SgrHom B C)
    : SgrHom A C.
Proof.
  sgr_simpl. exists (fun a : A => g (f a)). sgr.
Defined.

Definition SgrId (A : Sgr) : SgrHom A A.
Proof. sgr_simpl. exists (fun a : A => a). sgr. Defined.

Instance SgrCat : Cat :=
{
    Ob := Sgr;
    Hom := SgrHom;
    HomSetoid := SgrHomSetoid;
    comp := SgrComp;
    id := SgrId
}.
Proof.
  (* Proper *) sgr'. rewrite H, H0. sgr.
  (* Category laws *) all: sgr.
Defined.

Instance Sgr_init : Sgr :=
{
    carrier := Empty_set;
    op := fun (e : Empty_set) _ => match e with end
}.
Proof. sgr. Defined.

Definition Sgr_create (X : Sgr) : Hom Sgr_init X.
Proof.
  sgr_simpl. exists (fun e : Sgr_init => match e with end). sgr.
Defined.

Instance Sgr_has_init : has_init SgrCat :=
{
    init := Sgr_init;
    create := Sgr_create
}.
Proof. sgr. Defined.

Instance Sgr_term : Sgr :=
{
    carrier := unit;
    op := fun _ _ => tt
}.
Proof. sgr. Defined.

Definition Sgr_delete (X : Sgr) : Hom X Sgr_term.
Proof.
  sgr_simpl. exists (fun _ => tt). sgr.
Defined.

Instance Sgr_has_term : has_term SgrCat :=
{
    term := Sgr_term;
    delete := Sgr_delete
}.
Proof. sgr. Defined.

Instance Sgr_prod (X Y : Sgr) : Sgr := {}.
Proof.
  exact (prod X Y).
  destruct 1, 1. exact (op c c1, op c0 c2).
  destruct x, y, z. sgr'.
Defined.

Definition Sgr_proj1 (X Y : Sgr) : SgrHom (Sgr_prod X Y) X.
Proof.
  sgr_simpl. exists fst. destruct x, y. sgr.
Defined.

Definition Sgr_proj2 (X Y : Sgr) : SgrHom (Sgr_prod X Y) Y.
Proof.
  sgr_simpl. exists snd. destruct x, y. sgr.
Defined.

Definition Sgr_fpair (A B X : Sgr) (f : SgrHom X A) (g : SgrHom X B)
    : SgrHom X (Sgr_prod A B).
Proof.
  sgr_simpl. exists (fun x : X => (f x, g x)). sgr.
Defined.

Instance Sgr_has_products : has_products SgrCat :=
{
    prodOb := Sgr_prod;
    proj1 := Sgr_proj1;
    proj2 := Sgr_proj2;
    fpair := Sgr_fpair
}.
Proof.
  proper. rewrite H, H0. auto.
  repeat split; cat. rewrite H, H0. destruct (y x). auto.
Defined.

Instance Sgr_sum (X Y : Sgr) : Sgr :=
{
    carrier := sum X Y;
}.
Proof.
  destruct 1 as [x | y], 1 as [x' | y'].
    left. exact (op x x').
    left. exact x.
    left. exact x'.
    right. exact (op y y').
  destruct x, y, z; sgr.
Defined.

Definition Sgr_inl (X Y : Sgr) : SgrHom X (Sgr_sum X Y).
Proof. sgr_simpl. exists inl. sgr. Defined.

Definition Sgr_inr (X Y : Sgr) : SgrHom Y (Sgr_sum X Y).
Proof. sgr_simpl. exists inr. sgr. Defined.

(*Definition Sgr_copair (A B X : Sgr) (f : SgrHom A X) (g : SgrHom B X)
    : SgrHom (Sgr_sum A B) X.
Proof.
  red. exists (fun p : A + B =>
  match p with
    | inl a => f a
    | inr b => g b
  end).
  destruct x, y; destruct f, g; simpl; auto.  
*)

Instance Sgr_sumprod (X Y : Sgr) : Sgr :=
{
    carrier := sumprod X Y;
}.
Proof.
  destruct 1 as [x | y | x y], 1 as [x' | y' | x' y'].
    exact (inl' (op x x')).
    exact (pair' x y').
    exact (pair' (op x x') y').
    exact (pair' x' y).
    exact (inr' (op y y')).
    exact (pair' x' (op y y')).
    exact (pair' (op x x') y).
    exact (pair' x (op y y')).
    exact (pair' (op x x') (op y y')).
  destruct x, y, z; sgr.
Defined.

Definition Sgr_inl' (X Y : Sgr) : SgrHom X (Sgr_sumprod X Y).
Proof. sgr_simpl. exists (@inl' X Y). sgr. Defined.

Definition Sgr_inr' (X Y : Sgr) : SgrHom Y (Sgr_sumprod X Y).
Proof. sgr_simpl. exists (@inr' X Y). sgr. Defined.

(*Definition Sgr_copair' (A B X : Sgr) (f : SgrHom A X) (g : SgrHom B X)
    : SgrHom (Sgr_sumprod A B) X.
Proof.
  red. exists (fun p : sumprod A B =>
  match p with
    | inl' a => f a
    | inr' b => g b
    | pair' a b => op (f a) (g b)
  end).
  destruct x, y. simpl. auto.*)

(*Instance Sgr_has_coproducts : has_coproducts SgrCat :=
{
    coprodOb := Sgr_sum;
    coproj1 := Sgr_inl;
    coproj2 := Sgr_inr;
    copair := Sgr_copair;
}.*)

Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | cons_nel : A -> nel A -> nel A.

Arguments singl [A] _.
Arguments cons_nel [A] _ _.

Fixpoint app_nel {A : Type} (l1 l2 : nel A) : nel A :=
match l1 with
    | singl a => cons_nel a l2
    | cons_nel a l1' => cons_nel a (app_nel l1' l2)
end.

Theorem app_nel_assoc : forall (A : Type) (x y z : nel A),
    app_nel x (app_nel y z) = app_nel (app_nel x y) z.
Proof.
  induction x as [h | h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Qed.

Instance Sgr_freeprod (X Y : Sgr) : Sgr :=
{
    carrier := nel (X + Y);
    op := app_nel;
}.
Proof.
  apply app_nel_assoc.
Defined.

Definition Sgr_coproj1 (X Y : Sgr) : Hom X (Sgr_freeprod X Y).
Proof.
  sgr'. exists (fun x : X => singl (inl x)). simpl.
  intros.
Abort.

(* This can't be done. The free product of groups doesn't have
   coprojections in this category. To define them, an equivalence relation
   would be needed to make sure that singl (inl (op x y)) = cons_nel (inl x) (singl (inl y)) *)