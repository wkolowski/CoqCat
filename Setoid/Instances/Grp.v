Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".
Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/Instances".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export Mon1.

Set Universe Polymorphism.

Class Grp : Type :=
{
    carrier :> Mon;
    inv : carrier -> carrier;
    inv_l : forall x : carrier, op (inv x) x = neutr;
    inv_r : forall x : carrier, op x (inv x) = neutr
}.
  
Hint Resolve inv_l inv_r.

Coercion carrier : Grp >-> Mon.

Theorem inv_involutive : forall (G : Grp) (g : G),
    inv (inv g) = g.
Proof.
  intros. assert (H : op (inv (inv g)) (inv g) = neutr); auto.
  assert (H' : op (op (inv (inv g)) (inv g)) g = g).
    rewrite H. auto.
  rewrite <- assoc in H'. rewrite inv_l in H'. rewrite <- H' at 2. auto.
Qed.

Theorem inv_op : forall (G : Grp) (a b : G),
    inv (op a b) = op (inv b) (inv a).
Proof.
Abort.


Theorem inv_neutr : forall (G : Grp), inv neutr = neutr.
Proof.
Abort.
  
Ltac grp_simpl :=
match goal with
  | H : context [op (inv ?x) ?x] |- _ => rewrite inv_l in H
  | H : context [op ?x (inv ?x)] |- _ => rewrite inv_r in H
  | |- context [op (inv ?x) ?x] => rewrite inv_l
  | |- context [op ?x (inv ?x)] => rewrite inv_r
  | _ => idtac
end.

Ltac destr_grp :=
match goal with
  | G : Grp |- _ => destruct G as [G ? ? ?];
    destruct G as [G ? ? ?]; destruct G; destr_grp
  | _ => idtac
end.

Ltac grp := mon; repeat grp_simpl; mon.

Definition GrpHom (X Y : Grp) : Type := 
    {f : MonHom X Y | forall x : X, f (inv x) = inv (f x)}.

Definition GrpHom_MonHom (X Y : Grp) (f : GrpHom X Y)
    : MonHom X Y := proj1_sig f.
Coercion GrpHom_MonHom : GrpHom >-> MonHom.

Ltac destr_grphom :=
match goal with
  | f : GrpHom _ _ |- _ => destruct f as [[[f ?] ?] ?]; destr_grphom
  | f : Hom _ _ |- _ => destruct f as [[[f ?] ?] ?]; destr_grphom
  | _ => idtac
end; simpl in *.

Instance GrpHomSetoid (X Y : Grp) : Setoid (GrpHom X Y) :=
{
  equiv := fun f g : GrpHom X Y =>
      @equiv _ (SgrHomSetoid X Y) (proj1_sig f) (proj1_sig g)
}.
Proof. apply Setoid_kernel_equiv. Defined.

Definition GrpComp (X Y Z : Grp) (f : GrpHom X Y) (g : GrpHom Y Z)
    : GrpHom X Z.
Proof.
  red. destruct f as [f Hf0], g as [g Hg0]. exists (MonComp _ _ _ f g).
  destruct f as [[f Hf1] Hf2], g as [[g Hg1] Hg2]; simpl in *.
  intro. rewrite Hf0, Hg0. auto.
Defined.

Definition GrpId (X : Grp) : GrpHom X X.
Proof. red. exists (MonId X). simpl. auto. Defined.

Instance GrpCat : Cat :=
{
    Ob := Grp;
    Hom := GrpHom;
    HomSetoid := GrpHomSetoid;
    comp := GrpComp;
    id := GrpId;
}.
Proof.
  (* Proper *) repeat red; intros. destruct x, y, x0, y0; cat.
    eapply (@comp_Proper MonCat); auto.
  (* Category laws *) all: intros; destr_grphom; grp.
Defined.

Instance Grp_zero : Grp :=
{
    carrier := Mon_init;
    inv := fun _ => tt
}.
Proof. all: grp. Defined.

Definition Grp_create (X : Grp) : Hom Grp_zero X.
Proof.
  repeat red. exists (Mon_create X). grp. simpl.
Defined.
(*
Instance Mon_has_init : has_init MonCat :=
{
    init := Mon_init;
    create := Mon_create
}.
Proof. destruct f. mon. Defined.

Instance Mon_term : Mon :=
{
    sgr := Sgr_term;
    neutr := tt
}.
Proof. all: mon. Defined.

Definition Mon_Sgr_delete (X : Mon) : SgrHom X Mon_term.
Proof.
  repeat red; simpl. exists (fun _ => tt). auto.
Defined.

Definition Mon_delete (X : Mon) : Hom X Mon_term.
Proof.
  do 3 red. exists (Mon_Sgr_delete X). simpl. auto.
Defined.

Instance Mon_has_term : has_term MonCat :=
{
    term := Mon_term;
    delete := Mon_delete
}.
Proof. mon. Defined.

Instance Mon_has_zero : has_zero MonCat :=
{
    zero_is_initial := Mon_has_init;
    zero_is_terminal := Mon_has_term
}.
Proof. cat. Defined.

Instance Mon_prod (X Y : Mon) : Mon :=
{
    sgr := Sgr_prod X Y;
    neutr := (neutr, neutr);
}.
Proof. all: destruct a; mon. Defined.

Definition Mon_proj1 (X Y : Mon) : Hom (Mon_prod X Y) X.
Proof.
  repeat red; simpl. exists (Sgr_proj1 X Y). simpl. auto.
Defined.

Definition Mon_proj2 (X Y : Mon) : Hom (Mon_prod X Y) Y.
Proof.
  repeat red; simpl. exists (Sgr_proj2 X Y). simpl. auto.
Defined.

Definition Mon_diag (X Y Z : Mon) (f : MonHom X Y) (g : MonHom X Z)
    : MonHom X (Mon_prod Y Z).
Proof.
  red; simpl. exists (Sgr_diag _ _ _ f g).
  destruct f, g; simpl. mon.
Defined.

Instance Mon_has_products : has_products MonCat :=
{
    prod' := Mon_prod;
    proj1' := Mon_proj1;
    proj2' := Mon_proj2
}.
Proof.
  repeat red; simpl; intros. exists (Mon_diag _ _ _ f g). cat.
  destruct f, g, y; simpl in *. destruct x0, x1, x2; simpl in *.
  rewrite H, H0. destruct (x2 x). auto.
Defined.*)