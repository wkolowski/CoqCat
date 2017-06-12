Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Import Cat.Instances.Setoids.

Class Sgr : Type :=
{
    carrier : Setoid';
    op : carrier -> carrier -> carrier;
    assoc : forall x y z : carrier, op x (op y z) == op (op x y) z
}.

Coercion carrier : Sgr >-> Setoid'.

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
    forall x x' : ?X, ?f (?X_op x x') == ?Y_op (?f x) (?f x') |- _ =>
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
    let b := fresh S "_assoc" in destruct S as [S a b]; setoidob S
  | Ob _ => progress simpl in S; sgrob S
end; sgr_simpl.

Ltac sgrobs := repeat
match goal with
  | S : Sgr |- _ => sgrob S
  | S : Ob _ |- _ => sgrob S
end; sgr_simpl.

Definition SgrHom (A B : Sgr) : Type :=
    {f : SetoidHom A B | forall x y : A, f (op x y) == op (f x) (f y)}.

Definition SgrHom_Fun (A B : Sgr) (f : SgrHom A B)
    : SetoidHom A B := proj1_sig f.
Coercion SgrHom_Fun : SgrHom >-> SetoidHom.

Ltac sgrhom f := try intros until f;
match type of f with
  | SgrHom _ _ =>
      let a := fresh f "_pres_op" in destruct f as [f a];
      simpl in *; setoidhom f
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

Instance SgrHomSetoid (X Y : Sgr) : Setoid (SgrHom X Y) :=
{
    equiv := fun f g : SgrHom X Y => forall x : X, f x == g x
}.
Proof. solve_equiv. Defined.

Definition SgrComp (A B C : Sgr) (f : SgrHom A B) (g : SgrHom B C)
    : SgrHom A C.
Proof.
  sgr_simpl. exists (SetoidComp f g). sgr.
Defined.

Definition SgrId (A : Sgr) : SgrHom A A.
Proof.
  sgr_simpl. exists (SetoidId A). sgr.
Defined.

Instance SgrCat : Cat :=
{
    Ob := Sgr;
    Hom := SgrHom;
    HomSetoid := SgrHomSetoid;
    comp := SgrComp;
    id := SgrId
}.
Proof. all: sgr. Defined.

Instance Sgr_init : Sgr :=
{
    carrier := CoqSetoid_init;
    op := fun (e : Empty_set) _ => match e with end
}.
Proof. sgr. Defined.

Definition Sgr_create (X : Sgr) : Hom Sgr_init X.
Proof.
  sgr_simpl. exists (CoqSetoid_create X). sgr.
Defined.

Instance Sgr_has_init : has_init SgrCat :=
{
    init := Sgr_init;
    create := Sgr_create
}.
Proof. sgr. Defined.

Instance Sgr_term : Sgr :=
{
    carrier := CoqSetoid_term;
    op := fun _ _ => tt
}.
Proof. sgr. Defined.

Definition Sgr_delete (X : Sgr) : Hom X Sgr_term.
Proof.
  sgr_simpl. exists (CoqSetoid_delete X). sgr.
Defined.

Instance Sgr_has_term : has_term SgrCat :=
{
    term := Sgr_term;
    delete := Sgr_delete
}.
Proof. sgr. Defined.

Instance Sgr_prodOb (X Y : Sgr) : Sgr :=
{
    carrier := CoqSetoid_prodOb X Y;
    op := fun x y => (op (fst x) (fst y), op (snd x) (snd y))
}.
Proof. sgr. Defined.

Definition Sgr_proj1 (X Y : Sgr) : SgrHom (Sgr_prodOb X Y) X.
Proof.
  sgr_simpl. exists (CoqSetoid_proj1 X Y). sgr.
Defined.

Definition Sgr_proj2 (X Y : Sgr) : SgrHom (Sgr_prodOb X Y) Y.
Proof.
  sgr_simpl. exists (CoqSetoid_proj2 X Y). sgr.
Defined.

Definition Sgr_fpair (A B X : Sgr) (f : SgrHom X A) (g : SgrHom X B)
    : SgrHom X (Sgr_prodOb A B).
Proof.
  sgr_simpl. exists (CoqSetoid_fpair f g). sgr.
Defined.

Instance Sgr_has_products : has_products SgrCat :=
{
    prodOb := Sgr_prodOb;
    proj1 := Sgr_proj1;
    proj2 := Sgr_proj2;
    fpair := Sgr_fpair
}.
Proof.
  proper.
  repeat split; cat.
Defined.

Instance Sgr_sum (X Y : Sgr) : Sgr :=
{
    carrier := CoqSetoid_coprodOb X Y
}.
Proof.
  destruct 1 as [x | y], 1 as [x' | y'].
    left. exact (op x x').
    left. exact x.
    left. exact x'.
    right. exact (op y y').
  destruct x, y, z; sgr.
Defined.

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

(*Inductive freeprod_equiv {X Y : Setoid'}
    : nel (X + Y) -> nel (X + Y) -> Prop :=
    | equiv_singl1 : forall x : X, freeprod_equiv (singl x) (singl x)
    | equiv_singl*)

Fixpoint fp_equiv {X Y : Setoid'} (l1 l2 : nel (X + Y)) : Prop :=
match l1, l2 with
    | singl (inl x), singl (inl x') => x == x'
    | singl (inr y), singl (inr y') => y == y'
    | cons_nel (inl h1) t1, cons_nel (inl h2) t2 => h1 == h2 /\ fp_equiv t1 t2
    | cons_nel (inr h1) t1, cons_nel (inr h2) t2 => h1 == h2 /\ fp_equiv t1 t2
    | _, _ => False
end.

Ltac fp_equiv := intros; repeat
match goal with
    | x : _ + _ |- _ => destruct x; simpl in *
    | H : _ /\ _ |- _ => destruct H
    | |- _ /\ _ => split
    | |- ?x == ?x => reflexivity
    | H : ?P |- ?P => assumption
    | H : ?x == ?y |- ?y == ?x => symmetry; assumption
    | |- _ == _ => solve_equiv
    | H : False |- _ => inversion H
    | _ => eauto
end.

Theorem fp_equiv_refl : forall (X Y : Setoid') (l : nel (X + Y)),
    fp_equiv l l.
Proof.
  induction l as [| h t]; fp_equiv.
Qed.

Theorem fp_equiv_sym : forall (X Y : Setoid') (l1 l2 : nel (X + Y)),
    fp_equiv l1 l2 -> fp_equiv l2 l1.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; fp_equiv.
Qed.

Theorem fp_equiv_trans : forall (X Y : Setoid') (l1 l2 l3 : nel (X + Y)),
    fp_equiv l1 l2 -> fp_equiv l2 l3 -> fp_equiv l1 l3.
Proof.
  induction l1 as [| h1 t1]; destruct l2, l3; fp_equiv.
Qed.

Hint Resolve fp_equiv_refl fp_equiv_sym fp_equiv_trans.

Inductive fp_equiv2 {X Y : Setoid'} : nel (X + Y) -> nel (X + Y) -> Prop :=
    | singl_inl : forall x x' : X, x == x' ->
        fp_equiv2 (singl (inl x)) (singl (inl x'))
    | singl_inr : forall y y' : Y, y == y' ->
        fp_equiv2 (singl (inr y)) (singl (inr y'))
    | singl_mismatch1 : forall (x : X) (y : Y),
        fp_equiv2 (singl (inl x)) (singl (inr y))
    | singl_mismatch2 : forall (x : X) (y : Y),
        fp_equiv2 (singl (inr y)) (singl (inl x))
    | cons_inl : forall (h1 h2 : X) (t1 t2 : nel (X + Y)),
        h1 == h2 -> fp_equiv2 t1 t2 ->
        fp_equiv2 (cons_nel (inl h1) t1) (cons_nel (inl h2) t2)
    | cons_inr : forall (h1 h2 : Y) (t1 t2 : nel (X + Y)),
        h1 == h2 -> fp_equiv2 t1 t2 ->
        fp_equiv2 (cons_nel (inr h1) t1) (cons_nel (inr h2) t2)
    | cons_mismatch1 : forall (x : X) (y : Y) (t1 t2 : nel (X + Y)),
        fp_equiv2 t1 t2 ->
        fp_equiv2 (cons_nel (inl x) t1) (cons_nel (inr y) t2)
    | cons_mismatch2 : forall (x : X) (y : Y) (t1 t2 : nel (X + Y)),
        fp_equiv2 t1 t2 ->
        fp_equiv2 (cons_nel (inr y) t1) (cons_nel (inl x) t2).
(*    | trans : forall (l1 l2 l3 : nel (X + Y)),
        fp_equiv2 l1 l2 -> fp_equiv2 l2 l3 -> fp_equiv2 l1 l3.*)

Ltac fp_equiv2 := repeat
match goal with
    | x : _ + _ |- _ => destruct x; simpl in *
    | H : fp_equiv2 (singl _) _ |- _ => inversion H; subst; clear H
    | H : fp_equiv2 _ (singl _) |- _ => inversion H; subst; clear H
    | H : fp_equiv2 (cons_nel _ _) (cons_nel _ _) |- _ =>
        inversion H; subst; clear H
    | |- ?x == ?y => solve_equiv
    | H : ?P |- ?P => assumption
    | _ => constructor
end; eauto.

Theorem fp_equiv2_refl : forall (X Y : Setoid') (l : nel (X + Y)),
    fp_equiv2 l l.
Proof.
  induction l as [| h t]; fp_equiv2.
Qed.

Theorem fp_equiv2_sym : forall (X Y : Setoid') (l1 l2 : nel (X + Y)),
    fp_equiv2 l1 l2 -> fp_equiv2 l2 l1.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; intros;
  fp_equiv2.
Qed.

Theorem fp_equiv2_trans : forall (X Y : Setoid') (l1 l2 l3 : nel (X + Y)),
    fp_equiv2 l1 l2 -> fp_equiv2 l2 l3 -> fp_equiv2 l1 l3.
Proof.
  induction l1 as [| h1 t1]; destruct l2, l3; intros;
  try (fp_equiv2; fail).
    destruct a, s, s0; constructor.
      inversion H; inversion H0; subst; solve_equiv.
      inversion H; inversion H0; subst; solve_equiv.
      inversion H; inversion H0; subst; solve_equiv.
      inversion H; inversion H0; subst; solve_equiv.
Abort.

Instance CoqSetoid_freeprod (X Y : Setoid') : Setoid' :=
{
    carrier := nel (X + Y);
    setoid := {| equiv := @fp_equiv X Y |}
}.
Proof. solve_equiv. Defined.

Definition CoqSetoid_freeprod_coproj1 (X Y : Setoid')
    : SetoidHom X (CoqSetoid_freeprod X Y).
Proof.
  red. exists (fun x : X => singl (inl x)). proper.
Defined.

Definition CoqSetoid_freeprod_coproj2 (X Y : Setoid')
    : SetoidHom Y (CoqSetoid_freeprod X Y).
Proof.
  red. exists (fun y : Y => singl (inr y)). proper.
Defined.

Fixpoint Sgr_freeprod_op {X Y : Sgr} (l1 l2 : nel (X + Y))
    : nel (X + Y) :=
match l1, l2 with
    (*| singl (inl x), singl (inl x') => singl (inl (op x x'))
    | singl (inr y), singl (inr y') => singl (inr (op y y'))
    | singl s, l2 => cons_nel s l2
    | cons_nel (inl x) t1, cons_nel (inl x') t2 =>
        cons_nel (inl (op x x')) (Sgr_freeprod_op t1 t2)
    | cons_nel (inr y) t1, cons_nel (inr y') t2 =>
        cons_nel (inr (op y y')) (Sgr_freeprod_op t1 t2)
    | cons_nel h1 t1, cons_nel h2 t2 =>
        cons_nel h1 (cons_nel h2 (Sgr_freeprod_op t1 t2))*)
    | singl s, singl s' =>
        match s, s' with
            | inl x, inl x' => singl (inl (op x x'))
            | inr y, inr y' => singl (inr (op y y'))
            | _, _ => cons_nel s l2
        end
    | singl s, cons_nel h t =>
        match s, h with
            | inl x, inl x' => cons_nel (inl (op x x')) t
            | inr y, inr y' => cons_nel (inr (op y y')) t
            | _, _ => cons_nel s l2
        end
    | cons_nel h t, singl s =>
        match s, h with
            | inl x, inl x' => cons_nel (inl (op x x')) t
            | inr y, inr y' => cons_nel (inr (op y y')) t
            | _, _ => cons_nel s l2
        end
    | cons_nel h1 t1, cons_nel h2 t2 =>
        match h1, h2 with
            | inl x, inl x' => cons_nel (inl (op x x')) (Sgr_freeprod_op t1 t2)
            | inr y, inr y' => cons_nel (inr (op y y')) (Sgr_freeprod_op t1 t2)
            | _, _ => cons_nel h1 (cons_nel h2 (Sgr_freeprod_op t1 t2))
        end
end.

Theorem Sgr_freeprod_op_assoc : forall (X Y : Sgr) (l1 l2 l3 : nel (X + Y)),
    fp_equiv2 (Sgr_freeprod_op l1 (Sgr_freeprod_op l2 l3))
      (Sgr_freeprod_op (Sgr_freeprod_op l1 l2) l3).
Proof.
  induction l1 as [| h1 t1].
    destruct l2, l3.
    repeat match goal with
        | x : _ + _ |- _ => destruct x; simpl in *
    end; try constructor; sgr. Focus 2. 
        

Instance Sgr_freeprod (X Y : Sgr) : Sgr :=
{
    carrier := CoqSetoid_freeprod X Y;
    op := Sgr_freeprod_op
}.
Proof.
  intros. rewrite app_nel_assoc. reflexivity.
Defined.

Definition Sgr_coproj1 (X Y : Sgr) : Hom X (Sgr_freeprod X Y).
Proof.
  sgr_simpl. exists (CoqSetoid_freeprod_coproj1 X Y).
Abort.
