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
    neutr_l : forall a : sgr, op neutr a = a;
    neutr_r : forall a : sgr, op a neutr = a
}.

Coercion sgr : Mon >-> Sgr.

Hint Resolve neutr_l neutr_r.

Ltac mon_simpl := intros;
match goal with
  (* Neutral element of the operation. Not sure if works. *)
  | H : context [?op neutr _] |- _ => rewrite neutr_l in H
  | H : context [?op _ neutr] |- _ => rewrite neutr_r in H
  | |- context [?op neutr _] => rewrite neutr_l
  | |- context [?op _ neutr] => rewrite neutr_r
  | f : ?X -> ?Y, X_neutr : ?X, pres_neutr : ?f ?X_neutr = ?neutr2 |- _ =>
    match goal with
      (* This can't be here because H gets rewritten in itself and thus
         effectively destroyed. *)
      (*| H : context [f ?neutr1] |- _ => rewrite pres_neutr in H*)
      | |- context [?f ?neutr1] => rewrite pres_neutr
    end
  (* Homomorphisms *)
  | f : ?X -> ?Y, H : ?f neutr = neutr |- context [?f neutr] =>
    rewrite H
  | _ => idtac
end; sgr_simpl.

Ltac mon_simpl2 := intros;
match goal with
  | X_neutr : ?X |- _ => match goal with
    | op : X -> ?Y |- _ => clear
  end
end.

Ltac monob M := try intros until M;
match type of M with
  | Mon =>
    let a := fresh M "_neutr" in
    let b := fresh M "_neutr_l" in
    let c := fresh M "_neutr_r" in
      destruct M as [?M a b c]
  | Ob _ => progress simpl in M; monob M
end; simpl.

Ltac monob' M := monob M; sgrob M.

Ltac monobs_template tac := repeat
match goal with
  | M : Mon |- _ => tac M
  | M : Ob _ |- _ => tac M
end.

Ltac monobs := monobs_template monob.
Ltac monobs' := monobs_template monob'.

Definition MonHom (X Y : Mon) : Type :=
    {f : SgrHom X Y | f neutr = neutr}.

Definition MonHom_SgrHom (X Y : Mon) (f : MonHom X Y)
    : SgrHom X Y := proj1_sig f.
Coercion MonHom_SgrHom : MonHom >-> SgrHom.

Ltac monhom f := try intros until f;
match type of f with
    | MonHom _ _ =>
      let a := fresh f "_pres_neutr" in destruct f as [f a]
    | Hom _ _ => progress simpl in f; monhom f
end.

Ltac monhom' f := monhom f; sgrhom f.

Ltac monhoms_template tac := intros; repeat
match goal with
  | f : MonHom _ _ |- _ => tac f
  | f : Hom _ _ |- _ => tac f
end; mon_simpl.

Ltac monhoms := monhoms_template monhom.
Ltac monhoms' := monhoms_template monhom'.

Ltac mon_aux :=
match goal with
  | |- (_, _) = _ => f_equal
  | _ => cat
end.

Ltac mon' := repeat (mon_simpl || monobs || monhoms || mon_aux || cat).
Ltac mon := try (mon'; fail).

Instance MonHomSetoid (X Y : Mon) : Setoid (MonHom X Y) :=
{
    equiv := fun f g : MonHom X Y =>
      @equiv _ (SgrHomSetoid X Y) (proj1_sig f) (proj1_sig g)
}.
Proof. apply Setoid_kernel_equiv. Defined.

Definition MonComp (X Y Z : Mon) (f : MonHom X Y) (g : MonHom Y Z)
    : MonHom X Z.
Proof.
  mon_simpl. monhoms. exists (SgrComp _ _ _ f g).
  sgrhoms. rewrite f_pres_neutr, g_pres_neutr. auto.
Defined.

Definition MonId (X : Mon) : MonHom X X.
Proof. mon_simpl. exists (SgrId X). mon. Defined.

Instance MonCat : Cat :=
{
    Ob := Mon;
    Hom := MonHom;
    HomSetoid := MonHomSetoid;
    comp := MonComp;
    id := MonId
}.
Proof.
  (* Proper *) mon_simpl. monhoms. rewrite H, H0. auto.
  (* Category laws *) all: mon.
Defined.

Instance Mon_init : Mon :=
{
    sgr := Sgr_term;
    neutr := tt
}.
Proof. all: mon. Defined.

Definition Mon_Sgr_create (X : Mon) : SgrHom Mon_init X.
Proof.
  mon_simpl. exists (fun _ => neutr). auto.
Defined. 

Definition Mon_create (X : Mon) : Hom Mon_init X.
Proof.
  mon_simpl. exists (Mon_Sgr_create X). mon.
Defined.

Instance Mon_has_init : has_init MonCat :=
{
    init := Mon_init;
    create := Mon_create
}.
Proof. mon. Defined.

Instance Mon_term : Mon :=
{
    sgr := Sgr_term;
    neutr := tt
}.
Proof. all: mon. Defined.

Definition Mon_Sgr_delete (X : Mon) : SgrHom X Mon_term.
Proof.
  sgr_simpl. exists (fun _ => tt). auto.
Defined.

Definition Mon_delete (X : Mon) : Hom X Mon_term.
Proof.
  mon_simpl. exists (Mon_Sgr_delete X). mon.
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
Proof. mon. Defined.

Instance Mon_prod (X Y : Mon) : Mon :=
{
    sgr := Sgr_prod X Y;
    neutr := (neutr, neutr);
}.
Proof. all: destruct a; mon. Defined.

Definition Mon_proj1 (X Y : Mon) : Hom (Mon_prod X Y) X.
Proof.
  mon_simpl. exists (Sgr_proj1 X Y). mon.
Defined.

Definition Mon_proj2 (X Y : Mon) : Hom (Mon_prod X Y) Y.
Proof.
  mon_simpl. exists (Sgr_proj2 X Y). mon.
Defined.

Definition Mon_diag (X Y Z : Mon) (f : MonHom X Y) (g : MonHom X Z)
    : MonHom X (Mon_prod Y Z).
Proof.
  mon_simpl. exists (Sgr_diag _ _ _ f g). mon.
Defined.

Instance Mon_has_products : has_products MonCat :=
{
    prod' := Mon_prod;
    proj1' := Mon_proj1;
    proj2' := Mon_proj2
}.
Proof. (* mon_simpl seems too slow here *)
  repeat red. intros. exists (Mon_diag _ _ _ f g). mon'.
  rewrite H, H0. destruct (y x). auto.
Defined.
