Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export Cat.Instances.Setoids.

Require Import Cat.Nel.

Set Implicit Arguments.

Class Sgr : Type :=
{
    setoid :> Setoid';
    op : carrier -> carrier -> carrier;
    op_Proper :> Proper (equiv ==> equiv ==> equiv) op;
    assoc : forall x y z : carrier, op x (op y z) == op (op x y) z
}.

Coercion setoid : Sgr >-> Setoid'.

Class SgrHom (A B : Sgr) : Type :=
{
    func :> SetoidHom A B;
    pres_op : forall x y : A, func (op x y) == op (func x) (func y)
}.

Coercion func : SgrHom >-> SetoidHom.

Inductive exp (X : Sgr) : Type :=
    | Var : X -> exp X
    | Op : exp X -> exp X -> exp X
    | Mor : forall A : Sgr, SgrHom A X -> exp A -> exp X.

Arguments Var {X} _.
Arguments Op  {X} _ _.
Arguments Mor {X A} _ _.

Fixpoint expDenote {X : Sgr} (e : exp X) : X :=
match e with
    | Var v => v
    | Op e1 e2 => op (expDenote e1) (expDenote e2)
    | Mor f e' => f (expDenote e')
end.

Class Simplify (X : Sgr) (e : exp X) : Type :=
{
    simplify : exp X;
    simplify_spec : expDenote simplify == expDenote e
}.

Arguments Simplify {X} _.
Arguments simplify {X} _ {Simplify}.

#[refine]
Instance SimplifyOp {X : Sgr} {e1 e2 : exp X}
  (S1 : Simplify e1) (S2 : Simplify e2) : Simplify (Op e1 e2) | 10 :=
{
    simplify := Op (simplify e1) (simplify e2)
}.
Proof.
  cbn. rewrite !simplify_spec. reflexivity.
Defined.

#[refine]
Instance SimplifyMor {X Y : Sgr} (f : SgrHom X Y) (e : exp X)
  (S : Simplify e) : Simplify (Mor f e) | 10 :=
{
    simplify :=
      match simplify e with
          | Op e1' e2' => Op (Mor f e1') (Mor f e2')
          | e' => Mor f e'
      end
}.
Proof.
  destruct S, f, func0; cbn in *. destruct simplify0; cbn in *;
  rewrite <- simplify_spec0, ?pres_op0; reflexivity.
(*Restart.
  case_eq (simplify e); intros.
    rewrite <- H. cbn. rewrite simplify_spec. reflexivity.
    cbn. cbn in H. rewrite <- H. cbn. rewrite simplify_spec. reflexivity.
    
    cbn. destruct S. cbn in *. rewrite simplify_spec0.*)
Defined.

#[refine]
Instance SimplifyOther {X : Sgr} (e : exp X) : Simplify e | 100 :=
{
    simplify := e
}.
Proof.
  reflexivity.
Defined.

Fixpoint expDenoteNel {X : Sgr} (l : nel X) : X :=
match l with
    | singl x => x
    | h ::: t => op h (expDenoteNel t)
end.

Lemma expDenoteNel_app :
  forall (X : Sgr) (l1 l2 : nel X),
    expDenoteNel (l1 +++ l2) == op (expDenoteNel l1) (expDenoteNel l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    reflexivity.
    rewrite IHt1, assoc. reflexivity.
Qed.

Lemma expDenoteNel_hom :
  forall (X Y : Sgr) (f : SgrHom X Y) (l : nel X),
    expDenoteNel (nel_map f l) == f (expDenoteNel l).
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite pres_op, IHt. reflexivity.
Qed.

Fixpoint flatten {X : Sgr} (e : exp X) : nel X :=
match e with
    | Var v => singl v
    | Op e1 e2 => flatten e1 +++ flatten e2
    | Mor f e' => nel_map f (flatten e')
end.

Theorem flatten_correct :
  forall (X : Sgr) (e : exp X),
    expDenoteNel (flatten e) == expDenote e.
Proof.
  induction e; cbn.
    reflexivity.
    rewrite expDenoteNel_app, IHe1, IHe2. reflexivity.
    rewrite expDenoteNel_hom, IHe. reflexivity.
Qed.

Theorem sgr_reflect :
  forall (X : Sgr) (e1 e2 : exp X),
    expDenoteNel (flatten (simplify e1)) ==
    expDenoteNel (flatten (simplify e2)) ->
      expDenote e1 == expDenote e2.
Proof.
  intros. rewrite !flatten_correct, !simplify_spec in H. assumption.
Qed.

Class Reify (X : Sgr) (x : X) : Type :=
{
    reify : exp X;
    reify_spec : expDenote reify == x
}.

Arguments Reify {X} _.
Arguments reify {X} _ {Reify}.

#[refine]
Instance ReifyVar (X : Sgr) (x : X) : Reify x | 1 :=
{
    reify := Var x
}.
Proof. reflexivity. Defined.

#[refine]
Instance ReifyOp (X : Sgr) (a b : X) (Ra : Reify a) (Rb : Reify b)
    : Reify (@op X a b) | 0 :=
{
    reify := Op (reify a) (reify b)
}.
Proof.
  cbn. rewrite !reify_spec. reflexivity.
Defined.

#[refine]
Instance ReifyMor (X Y : Sgr) (f : SgrHom X Y) (x : X) (Rx : Reify x)
    : Reify (f x) | 0 :=
{
    reify := Mor f (reify x)
}.
Proof.
  cbn. rewrite !reify_spec. reflexivity.
Defined.

Ltac reflect_sgr := simpl; intros;
match goal with
    | |- ?e1 == ?e2 =>
        change (expDenote (reify e1) == expDenote (reify e2));
        apply sgr_reflect; simpl
end.

Ltac sgr_simpl := repeat red; simpl in *; intros.

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

Ltac sgr := intros; try (reflect_sgr; try reflexivity; fail); repeat
match goal with
    | |- _ == _ => reflect_sgr; reflexivity
    | |- Equivalence _ => solve_equiv
    | |- Proper _ _ => proper
    | _ => sgr_simpl || sgrobs || sgrhoms || cat
end.

Goal forall (X : Sgr) (a b c : X),
  op a (op b c) == op (op a b) c.
Proof.
  reflect_sgr. reflexivity.
Qed.

Goal forall (X : Sgr) (f : SgrHom X X) (a b : X),
  f (op a b) == op (f a) (f b).
Proof.
  reflect_sgr. reflexivity.
Qed.

#[refine]
Instance SgrHomSetoid (X Y : Sgr) : Setoid (SgrHom X Y) :=
{
    equiv := fun f g : SgrHom X Y => forall x : X, f x == g x
}.
Proof. sgr. Defined.

Definition SgrComp (A B C : Sgr) (f : SgrHom A B) (g : SgrHom B C)
    : SgrHom A C.
Proof.
  exists (SetoidComp f g). sgr.
Defined.

Definition SgrId (A : Sgr) : SgrHom A A.
Proof.
  exists (SetoidId A). sgr.
Defined.

#[refine]
Instance SgrCat : Cat :=
{
    Ob := Sgr;
    Hom := SgrHom;
    HomSetoid := SgrHomSetoid;
    comp := SgrComp;
    id := SgrId
}.
Proof. Time all: sgr. Defined.

#[refine]
Instance Sgr_init : Sgr :=
{
    setoid := CoqSetoid_init;
    op := fun (e : Empty_set) _ => match e with end
}.
Proof. all: sgr. Defined.

Definition Sgr_create (X : Sgr) : Hom Sgr_init X.
Proof.
  sgr_simpl. exists (CoqSetoid_create X). sgr.
Defined.

#[refine]
Instance Sgr_has_init : has_init SgrCat :=
{
    init := Sgr_init;
    create := Sgr_create
}.
Proof. sgr. Defined.

#[refine]
Instance Sgr_term : Sgr :=
{
    setoid := CoqSetoid_term;
    op := fun _ _ => tt
}.
Proof. all: sgr. Defined.

Definition Sgr_delete (X : Sgr) : Hom X Sgr_term.
Proof.
  exists (CoqSetoid_delete X). sgr.
Defined.

#[refine]
Instance Sgr_has_term : has_term SgrCat :=
{
    term := Sgr_term;
    delete := Sgr_delete
}.
Proof. sgr. Defined.

#[refine]
Instance Sgr_prodOb (X Y : Sgr) : Sgr :=
{
    setoid := CoqSetoid_prodOb X Y;
    op := fun x y => (op (fst x) (fst y), op (snd x) (snd y))
}.
Proof.
  proper. destruct H, H0. rewrite H, H0, H1, H2. split; reflexivity.
  sgr.
Defined.

Definition Sgr_proj1 (X Y : Sgr) : SgrHom (Sgr_prodOb X Y) X.
Proof.
  exists (CoqSetoid_proj1 X Y). sgr.
Defined.

Definition Sgr_proj2 (X Y : Sgr) : SgrHom (Sgr_prodOb X Y) Y.
Proof.
  exists (CoqSetoid_proj2 X Y). sgr.
Defined.

Definition Sgr_fpair (A B X : Sgr) (f : SgrHom X A) (g : SgrHom X B)
    : SgrHom X (Sgr_prodOb A B).
Proof.
  exists (CoqSetoid_fpair f g). split; sgr.
Defined.

#[refine]
Instance Sgr_has_products : has_products SgrCat :=
{
    prodOb := Sgr_prodOb;
    proj1 := Sgr_proj1;
    proj2 := Sgr_proj2;
    fpair := Sgr_fpair
}.
Proof. all: sgr. Defined.

#[refine]
Instance Sgr_sum (X Y : Sgr) : Sgr :=
{
    setoid := CoqSetoid_coprodOb X Y
}.
Proof.
  destruct 1 as [x | y], 1 as [x' | y']; cat.
 (*   left. exact (op x x').
    left. exact x.
    left. exact x'.
    right. exact (op y y').*)
  proper. repeat
  match goal with
      | H : match ?x with _ => _ end |- _ => destruct x
      | |- match ?x with _ => _ end => destruct x
      | H : False |- _ => inversion H
  end; auto.
  Time destruct x, y, z; sgr.
Defined.

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

#[refine]
Instance CoqSetoid_nel (X : Setoid') : Setoid' :=
{
    carrier := nel X;
    setoid := {| equiv := @equiv_nel X |}
}.
Proof. sgr. Defined.

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

Definition Sgr_freeprod_setoid_coproj1 (X Y : Sgr)
    : SetoidHom X (Sgr_freeprod_setoid X Y).
Proof.
  exists (fun x : X => singl (inl x)). sgr.
Defined.

Definition Sgr_freeprod_setoid_coproj2 (X Y : Sgr)
    : SetoidHom Y (Sgr_freeprod_setoid X Y).
Proof.
  exists (fun y : Y => singl (inr y)). sgr.
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
    fpeq4 l1 l1' -> fpeq4 l2 l2' -> fpeq4 (l1 +++ l2) (l1' +++ l2').
Proof.
  unfold fpeq4. induction l1 as [| h1 t1].
    simpl; intros. fpeq4. destruct l2.
      fpeq4. Focus 2.
Abort.

(*Instance Sgr_freeprod (X Y : Sgr) : Sgr :=
{
    setoid := Sgr_freeprod_setoid X Y;
    op := app_nel
}.
Proof.
  proper. induction x as [| h t].
    destruct y, x0, y0, a, s, s0, s1; simpl in *; repeat
    match goal with | |- op _ _ == op _ _ => apply WHUUUT end; solve_equiv.
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
  red.
Abort.*)

Class SgrWut : Type :=
{
    sgr :> Sgr;
    wut : sgr;
    wut_eq : op wut wut == wut
}.

Coercion sgr : SgrWut >-> Sgr.

#[refine]
Instance Simplify_wut_eq (X : SgrWut) : Simplify (Op (Var wut) (Var wut))
    | 11 :=
{
    simplify := Var wut
}.
Proof.
  cbn. rewrite wut_eq. reflexivity.
Defined.

(*Instance Reify_wut_eq (X : SgrWut) : Reify (op wut wut) :=
{
    reify := Var wut
}.
Proof.
  cbn. rewrite wut_eq. reflexivity.
Defined.*)

Ltac reflect_sgr2 := intros; do 2 (rewrite <- reify_spec; symmetry);
  apply sgr_reflect; cbn.

Ltac reflect_sgr3 := intros; repeat progress
  (do 2 (rewrite <- reify_spec, <- simplify_spec at 1; symmetry); cbn);
  reflect_sgr.

Goal forall (X : SgrWut) (a b c : X),
  op a (op b c) == op (op a b) c.
Proof.
  reflect_sgr2. reflexivity.
Qed.

Goal forall (X : SgrWut) (a b c : X),
  op a (op wut wut) == op a wut.
Proof.
  intros.
  reflect_sgr.
  reflect_sgr2.
  reflect_sgr3.
  rewrite <- reify_spec. rewrite <- simplify_spec. cbn.
  (* instantiate (1 := SimplifyOp (SimplifyOther _) (Simplify_wut_eq X)).*)
  (* TODO: zdechło *)
  cbn.
Abort.

Theorem simplify_correct2 :
  forall (X : Sgr) (e : exp X) (S : Simplify e),
    expDenote (simplify e) == expDenote e.
Proof.
  destruct S; cbn; intros. assumption.
Defined.

Goal forall (X : SgrWut) (a b c : X),
  op a (op wut wut) == op a wut.
Proof.
  intros.
  reflect_sgr.
  reflect_sgr2.
  reflect_sgr3.
  rewrite <- reify_spec. rewrite <- simplify_correct2. cbn.
  
  instantiate (1 := SimplifyOp (SimplifyOther _) (Simplify_wut_eq X)).
  cbn. reflexivity.
Qed.

Axiom troll : forall (X : Sgr) (x : X), op x x == x.

#[refine]
Instance Simplify_troll (X : Sgr) (x : X) : Simplify (Op (Var x) (Var x))
    | 1 :=
{
    simplify := Var x
}.
Proof.
  cbn. rewrite troll. reflexivity.
Defined.

Goal forall (X : Sgr) (a b c : X),
  op a (op b b) == op a b.
Proof.
  intros.
  reflect_sgr.
  reflect_sgr2.
  reflect_sgr3. try reflexivity.
Qed.

(* Does it work recursively? *)
Goal forall (X : Sgr) (x : X),
  op (op x x) (op x x) == x.
Proof.
  reflect_sgr3. reflexivity.
Qed.

(* TODO: Note to self: class-based Simplify could work, but the instance
   Simplify_wut_eq for some reason can't be found by the resolution engine. *)

Goal forall (X : SgrWut) (a b c : X),
  op (op a wut) (op wut b) == op a (op wut b).
Proof.
  reflect_sgr3.
Abort.