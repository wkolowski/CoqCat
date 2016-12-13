Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".
Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/Instances".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export Sgr.

Set Universe Polymorphism.

(* This implementation won't use Sgr directly, only for coercions. *)
Class Mon : Type :=
{
    carrier : Type;
    op : carrier -> carrier -> carrier;
    assoc : forall x y z : carrier, op x (op y z) = op (op x y) z;
    neutr : carrier;
    neutr_l : forall a : carrier, op a neutr = a;
    neutr_r : forall a : carrier, op neutr a = a
}.

Hint Resolve assoc neutr_l neutr_r.

Instance Mon_to_Sgr (M : Mon) : Sgr :=
{
    carrier := carrier;
    op := op;
    assoc := assoc;
}.
Coercion Mon_to_Sgr : Mon >-> Sgr.

Ltac mon_simpl :=
match goal with
  | H : context [op neutr _] |- _ => rewrite neutr_l in H
  | H : context [op _ neutr] |- _ => rewrite neutr_r in H
  | |- context [op neutr _] => rewrite neutr_l
  | |- context [op _ neutr] => rewrite neutr_r
end.

Ltac destr_mon :=
match goal with
  | M : Mon |- _ => destruct M; destr_mon
  | _ => idtac
end.

Definition MonHom (X Y : Mon) : Type :=
    {f : X -> Y | f neutr = neutr /\
      forall x y : carrier, op (f x) (f y) = f (op x y)}.

Definition MonHom_SgrHom (X Y : Mon) (f : MonHom X Y)
    : SgrHom X Y.
Proof.
  red. destruct f as [f [H1 H2]]. exists f. simpl. auto.
Defined.
Coercion MonHom_SgrHom : MonHom >-> SgrHom.

Ltac destr_monhom := intros;
match goal with
    | u : MonHom _ _ |- _ => destruct u as [u [?u ?u]]; destr_monhom
    | u : Hom _ _ |- _ => destruct u as [u [?u ?u]]; destr_monhom
    | _ => idtac
end.

Ltac destr := destr_mon; destr_monhom.

Ltac mon := cat; repeat mon_simpl;
match goal with
  | |- (_, _) = _ => f_equal
  | _ => cat
end; cat.

Instance MonHomSetoid (X Y : Mon) : Setoid (MonHom X Y) :=
{
    equiv := fun f g : MonHom X Y =>
      forall x : X, f x = g x
}.
Proof. cat; red; intros. rewrite H, H0. auto. Defined.

Definition MonComp (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z)
    : MonHom X Z.
Proof.
  red. destruct f as [f [Hf1 Hf2]], g as [g [Hg1 Hg2]].
  exists (fun x : X => g (f x)). mon.
    rewrite Hf1, Hg1. auto.
    rewrite Hg2, Hf2. auto.
Defined.

Definition MonId (X : Mon) : MonHom X X.
Proof. red. exists (fun x : X => x). mon. Defined.

Instance MonCat : Cat :=
{
    Ob := Mon;
    Hom := MonHom;
    HomSetoid := MonHomSetoid;
    comp := MonComp;
    id := MonId
}.
Proof.
  (* Proper *) repeat red; intros. destruct x, y, x0, y0; cat.
    rewrite H0, H. auto.
  (* Category laws *) all: intros; destr_monhom; mon.
Defined.

Instance Mon_zero : Mon :=
{
    carrier := unit;
    op := fun _ _ => tt;
    neutr := tt;
}.
Proof. all: mon. Defined.

Definition Mon_create (X : Mon) : Hom Mon_zero X.
Proof.
  repeat red. exists (fun _ => neutr). mon.
Defined.

Instance Mon_has_init : has_init MonCat :=
{
    init := Mon_zero;
    create := Mon_create
}.
Proof. destr_monhom; mon. Defined.

Definition Mon_delete (X : Mon) : Hom X Mon_zero.
Proof.
  repeat red. exists (fun _ => tt). mon.
Defined.

Instance Mon_has_term : has_term MonCat :=
{
    term := Mon_zero;
    delete := Mon_delete
}.
Proof. mon. Defined.

Instance Mon_has_zero : has_zero MonCat :=
{
    zero_is_initial := Mon_has_init;
    zero_is_terminal := Mon_has_term
}.
Proof. mon. Defined.

Instance Mon_prod (X Y : Mon) : Mon :=
{
    carrier := X * Y;
    op := fun p1 p2 : X * Y => (op (fst p1) (fst p2), op (snd p1) (snd p2));
    neutr := (neutr, neutr);
}.
Proof. all: try destruct a; mon. Defined.

Definition Mon_proj1 (X Y : Mon) : Hom (Mon_prod X Y) X.
Proof.
  repeat red; simpl. exists fst. mon.
Defined.

Definition Mon_proj2 (X Y : Mon) : Hom (Mon_prod X Y) Y.
Proof.
  repeat red; simpl. exists snd. mon.
Defined.

Definition Mon_diag (X Y Z : Mon) (f : MonHom X Y) (g : MonHom X Z)
    : MonHom X (Mon_prod Y Z).
Proof.
  red; simpl. exists (fun x : X => (f x, g x)).
  destr_monhom; mon.
Defined.

Instance Mon_has_products : has_products MonCat :=
{
    prod' := Mon_prod;
    proj1' := Mon_proj1;
    proj2' := Mon_proj2
}.
Proof.
  repeat red; simpl; intros. exists (Mon_diag _ _ _ f g).
  repeat (red || split); intros; destr_monhom; simpl in *; auto.
  destruct H; rewrite H, H0. destruct (y x). mon.
Defined.