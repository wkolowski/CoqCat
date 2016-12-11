Add Rec LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid".
Add LoadPath "/home/zeimer/Code/Coq/CoqCat/Setoid/Instances".

Require Export Cat.
Require Import InitTerm.
Require Import BinProdCoprod.

Require Export Sgr.

Set Universe Polymorphism.

Class Mon : Type :=
{
    sgr :> Sgr;
    neutr : sgr;
    neutr_l : forall a : sgr, op a neutr = a;
    neutr_r : forall a : sgr, op neutr a = a
}.

Hint Resolve neutr_l neutr_r.

Coercion sgr : Mon >-> Sgr.

Ltac mon_simpl :=
match goal with
  | H : context [op neutr _] |- _ => rewrite neutr_l in H
  | H : context [op _ neutr] |- _ => rewrite neutr_r in H
  | |- context [op neutr _] => rewrite neutr_l
  | |- context [op _ neutr] => rewrite neutr_r
end.

Ltac mon := cat; repeat mon_simpl;
match goal with
  | |- (_, _) = _ => f_equal
  | _ => cat
end; cat.

Definition MonHom (X Y : Mon) : Type :=
    {f : SgrHom X Y | f neutr = neutr}.

Definition MonHom_SgrHom (X Y : Mon) (f : MonHom X Y)
    : SgrHom X Y := proj1_sig f.
Coercion MonHom_SgrHom : MonHom >-> SgrHom.

Instance MonHomSetoid (X Y : Mon) : Setoid (MonHom X Y) :=
{
    equiv := fun f g : MonHom X Y =>
      @equiv _ (SgrHomSetoid X Y) (proj1_sig f) (proj1_sig g)
}.
Proof. apply Setoid_kernel_equiv. Defined.

Definition MonComp (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z)
    : MonHom X Z.
Proof.
  red. destruct f as [f Hf], g as [g Hg]. exists (SgrComp _ _ _ f g).
  destruct f as [f Hf'], g as [g Hg']; simpl in *.
  rewrite Hf, Hg. reflexivity.
Defined.

Definition MonId (X : Mon) : MonHom X X.
Proof. red. exists (SgrId X). simpl. auto. Defined.

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
    eapply (@comp_Proper SgrCat); auto.
  (* Category laws *) all: intros; repeat match goal with
    | f : MonHom _ _ |- _ => destruct f
  end; simpl.
    apply (@comp_assoc SgrCat).
    apply (@id_left SgrCat).
    apply (@id_right SgrCat).
Defined.

Instance Mon_init : Mon :=
{
    sgr := Sgr_term;
    neutr := tt
}.
Proof. all: mon. Defined.

Definition Mon_Sgr_create (X : Mon) : SgrHom Mon_init X.
Proof. red. exists (fun _ => neutr). auto. Defined. 

Definition Mon_create (X : Mon) : Hom Mon_init X.
Proof.
  repeat red. exists (Mon_Sgr_create X). simpl. auto.
Defined.

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
Defined.

Definition Mon_Sgr_coproj1 (X Y : Mon) : SgrHom X (Sgr_prod X Y).
Proof.
  red. exists (fun x : X => (x, neutr)). mon.
Defined.

Definition Mon_coproj1 (X Y : Mon) : Hom X (Mon_prod X Y).
Proof.
  repeat red. exists (Mon_Sgr_coproj1 X Y). mon.
Defined.

(*Definition Mon_Sgr_coproj2 (X Y : Mon) : SgrHom Y (Sgr_prod X Y).
Proof.
  red. exists (fun y : Y => (neutr, y)). mon.
Defined.

Definition Mon_coproj2 (X Y : Mon) : Hom Y (Mon_prod X Y).
Proof.
  repeat red. exists (Mon_Sgr_coproj2 X Y). mon.
Defined.

Definition Mon_Sgr_codiag {X Y Z : Mon} (f : MonHom X Z) (g : MonHom Y Z)
    : SgrHom (Sgr_prod X Y) Z.
Proof.
  repeat red. (* exists (fun p : X * Y => op (f (fst p)) (g (snd p))).
  destruct x, y, f as [[f Hf] Hf'], g as [[g Hg] Hg']; simpl in *.
  rewrite Hf, Hg.*)
  exists (fun p : X * Y => f (fst p)).
  repeat destruct x, y, f, g; destruct x, x0; simpl in *. mon.
Defined.

Definition Mon_codiag {X Y Z : Mon} (f : MonHom X Z) (g : MonHom Y Z)
    : MonHom (Mon_prod X Y) Z.
Proof.
  red. exists (Mon_Sgr_codiag f g). destruct f; simpl. auto.
Defined.

Instance Mon_has_coproducts : has_coproducts MonCat :=
{
    coprod := Mon_prod;
    coproj1 := Mon_coproj1;
    coproj2 := Mon_coproj2
}.
Proof.
  repeat red; intros. exists (Mon_codiag f g).
  mon. destruct f, g. simpl. destruct x0, x1. simpl in *.*)