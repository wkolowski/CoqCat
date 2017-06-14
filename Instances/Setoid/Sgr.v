Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Import Cat.Instances.Setoids.

Class Sgr : Type :=
{
    carrier : Setoid';
    op : carrier -> carrier -> carrier;
    op_Proper : Proper (equiv ==> equiv ==> equiv) op;
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
    let a' := fresh S "_op_Proper" in 
    let b := fresh S "_assoc" in destruct S as [S a a' b]; setoidob S
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
Proof. proper. all: sgr. Defined.

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
Proof. proper. sgr. Defined.

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
Proof.
  proper. destruct H, H0. split; apply op_Proper; auto.
  sgr.
Defined.

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
  proper. repeat
  match goal with
      | H : match ?x with _ => _ end |- _ => destruct x
      | |- match ?x with _ => _ end => destruct x
      | |- op _ _ == op _ _ => apply op_Proper
      | H : False |- _ => inversion H
  end; auto.
  destruct x, y, z; sgr.
Defined.

Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | cons_nel : A -> nel A -> nel A.

Arguments singl [A] _.
Arguments cons_nel [A] _ _.

Notation "h ::: t" := (cons_nel h t) (right associativity, at level 30).

Fixpoint app_nel {A : Type} (l1 l2 : nel A) : nel A :=
match l1 with
    | singl a => cons_nel a l2
    | a ::: l1' => cons_nel a (app_nel l1' l2)
end.

Theorem app_nel_assoc : forall (A : Type) (x y z : nel A),
    app_nel x (app_nel y z) = app_nel (app_nel x y) z.
Proof.
  induction x as [h | h t]; simpl; intros.
    trivial.
    rewrite IHt. trivial.
Qed.

Fixpoint equiv_nel {X : Setoid'} (l1 l2 : nel X) : Prop :=
match l1, l2 with
    | singl h, singl h' => h == h'
    | h ::: t, h' ::: t' => h == h' /\ equiv_nel t t'
    | _, _ => False
end.

Theorem equiv_nel_refl : forall (X : Setoid') (l : nel X),
    equiv_nel l l.
Proof.
  induction l as [| h t]; simpl; try rewrite IHt; solve_equiv.
Qed.

Theorem equiv_nel_sym : forall (X : Setoid') (l1 l2 : nel X),
    equiv_nel l1 l2 -> equiv_nel l2 l1.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; simpl;
  intros; solve_equiv.
Qed.

Theorem equiv_nel_trans : forall (X : Setoid') (l1 l2 l3 : nel X),
    equiv_nel l1 l2 -> equiv_nel l2 l3 -> equiv_nel l1 l3.
Proof.
  induction l1 as [| h1 t1]; destruct l2, l3; solve_equiv.
Qed.

Hint Resolve equiv_nel_refl equiv_nel_sym equiv_nel_trans.

Instance CoqSetoid_nel (X : Setoid') : Setoid' :=
{
    carrier := nel X;
    setoid := {| equiv := @equiv_nel X |}
}.
Proof. solve_equiv. Defined.


Fixpoint normalize {X Y : Sgr} (l : nel (X + Y)) {struct l} : nel (X + Y) :=
match l with
    | singl s => singl s
    | inl x ::: singl (inl x') => singl (inl (op x x'))
    | inr y ::: singl (inr y') => singl (inr (op y y'))
    | inl _ ::: singl (inr _) => l
    | inr _ ::: singl (inl _) => l
    | inl x ::: t =>
        match normalize t with
            | singl (inl x') => singl (inl (op x x'))
            | inl x' ::: t' => inl (op x x') ::: t'
            | t' => inl x ::: t'
        end
    | inr y ::: t =>
        match normalize t with
            | singl (inr y') => singl (inr (op y y'))
            | inr y' ::: t' => inr (op y y') ::: t'
            | t' => inr y ::: t'
        end
end.

Instance Sgr_freeprod_setoid (X Y : Sgr) : Setoid' :=
{
    carrier := nel (X + Y);
    setoid := Setoid_kernel_equiv
      (@CoqSetoid_nel (CoqSetoid_coprodOb X Y)) (@normalize X Y)
}.
(*Proof. solve_equiv. Defined.*)

Definition Sgr_freeprod_setoid_coproj1 (X Y : Sgr)
    : SetoidHom X (Sgr_freeprod_setoid X Y).
Proof.
  red. exists (fun x : X => singl (inl x)). proper.
Defined.

Definition Sgr_freeprod_setoid_coproj2 (X Y : Sgr)
    : SetoidHom Y (Sgr_freeprod_setoid X Y).
Proof.
  red. exists (fun y : Y => singl (inr y)). proper.
Defined.

(*Fixpoint fp_equiv {X Y : Setoid'} (l1 l2 : nel (CoqSetoid_coprodOb X Y))
    : Prop :=
match l1, l2 with
    | singl h, singl h' => h == h'
    | h1 ::: t1, h2 ::: t2 => h1 == h2 /\ fp_equiv t1 t2
    | _, _ => False
end.*)

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

Definition fpeq4 {X Y : Sgr} (l1 l2 : nel (X + Y)) : Prop :=
    fp_equiv (normalize l1) (normalize l2).

Ltac fpeq4 := unfold fpeq4; repeat
match goal with
    | x : _ + _ |- _ => destruct x; simpl in *
    | H : match normalize ?l with | _ => _ end |- _ =>
        destruct (normalize l); simpl in *
    | |- match normalize ?l with | _ => _ end =>
        destruct (normalize l); simpl in *
    | _ => solve_equiv
end.

Theorem fpeq4_refl : forall (X Y : Sgr) (l : nel (X + Y)),
    fpeq4 l l.
Proof.
  unfold fpeq4. induction l as [| h [| h' t]]; fpeq4.
Qed.

Theorem fpeq4_sym : forall (X Y : Sgr) (l1 l2 : nel (X + Y)),
    fpeq4 l1 l2 -> fpeq4 l2 l1.
Proof.
  unfold fpeq4. induction l1 as [| h [| h' t]]; fpeq4.
Qed.

Theorem fpeq4_trans : forall (X Y : Sgr) (l1 l2 l3 : nel (X + Y)),
    fpeq4 l1 l2 -> fpeq4 l2 l3 -> fpeq4 l1 l3.
Proof.
  unfold fpeq4. induction l1 as [| h1 t1]; fpeq4.
Qed.

Hint Resolve fpeq4_refl fpeq4_sym fpeq4_trans.

Theorem app_nel_Proper : forall (X Y : Sgr) (l1 l1' l2 l2' : nel (X + Y)),
    fpeq4 l1 l1' -> fpeq4 l2 l2' -> fpeq4 (app_nel l1 l2) (app_nel l1' l2').
Proof.
  unfold fpeq4. induction l1 as [| h1 t1].
    simpl; intros. fpeq4. destruct l2.
      fpeq4. Focus 2.
Abort.

Instance Sgr_freeprod (X Y : Sgr) : Sgr :=
{
    carrier := Sgr_freeprod_setoid X Y;
    op := app_nel
}.
Proof.
  proper. pose op_Proper. induction x as [| h t].
    destruct y, x0, y0, a, s, s0, s1; simpl in *; repeat
    match goal with | |- op _ _ == op _ _ => apply op_Proper end; solve_equiv.
  intros. rewrite app_nel_assoc. reflexivity.
Defined.

Definition Sgr_coproj1 (X Y : Sgr)
    : SgrHom X (Sgr_freeprod X Y).
Proof.
  red. exists (Sgr_freeprod_setoid_coproj1 X Y).
  simpl. unfold fpeq4; simpl. reflexivity.
Defined.

Definition Sgr_coproj2 (X Y : Sgr)
    : SgrHom Y (Sgr_freeprod X Y).
Proof.
  red. exists (Sgr_freeprod_setoid_coproj2 X Y).
  simpl; unfold fpeq4; simpl. reflexivity.
Defined.

Fixpoint freemap {X Y A : Sgr} (f : SgrHom X A) (g : SgrHom Y A)
    (l : nel (X + Y)) : nel A :=
match l with
    | singl (inl x) => singl (f x)
    | singl (inr y) => singl (g y)
    | inl x ::: t => f x ::: freemap f g t
    | inr y ::: t => g y ::: freemap f g t
end.

Fixpoint fold {A : Sgr} (l : nel A) : A :=
match l with
    | singl a => a
    | a ::: singl a' => op a a'
    | a ::: t => op a (fold t)
end.

Theorem fold_Proper : forall (A : Sgr) (l1 l2 : nel A),
    equiv_nel l1 l2 -> fold l1 == fold l2.
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; simpl; cat.
  destruct t1, t2; simpl in *.
    rewrite H, H0.
    

Definition Sgr_setoid_copair (X Y A : Sgr) (f : SgrHom X A) (g : SgrHom Y A)
    : SetoidHom (Sgr_freeprod X Y) A.
Proof.
  red. exists (fun l => fold (freemap f g l)). proper. fpeq4.
  do 2 red; simpl. unfold fpeq4.
  induction x as [| h t]; simpl; intro.
    destruct a, (normalize y).
    destruct y as [| h' t'].
      fpeq4; sgr.
      intros. simpl in H.

Definition Sgr_copair (X Y A : Sgr) (f : SgrHom X A) (g : SgrHom Y A)
    : SgrHom (Sgr_freeprod X Y) A.
Proof.
  red. exists 