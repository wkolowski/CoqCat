From Cat Require Export Cat.

Set Implicit Arguments.

Class HasInit (C : Cat) : Type :=
{
  init : Ob C;
  create : forall X : Ob C, Hom init X;
  create_unique : forall (X : Ob C) (f : Hom init X), f == create X;
}.

Arguments init _ {HasInit}.

Ltac init := intros; repeat
match goal with
| |- context [?f] =>
  match type of f with
  | Hom (init _) _ => rewrite (create_unique _ f)
  end
| |- ?x == ?x => reflexivity
end; try (cat; fail).

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  delete : forall X : Ob C, Hom X term;
  delete_unique : forall (X : Ob C) (f : Hom X term), f == delete X;
}.

Arguments term _ {HasTerm}.

Class HasZero (C : Cat) : Type :=
{
  zero_is_initial :> HasInit C;
  zero_is_terminal :> HasTerm C;
  initial_is_terminal : init C = term C
}.

Coercion zero_is_initial : HasZero >-> HasInit.
Coercion zero_is_terminal : HasZero >-> HasTerm.

Definition zero_ob (C : Cat) {hz : HasZero C} : Ob C := init C.
Definition zero_mor {C : Cat} {hz : HasZero C} (X Y : Ob C) : Hom X Y.
Proof.
  pose (f := delete X). pose (g := create Y).
  rewrite initial_is_terminal in g. exact (f .> g).
Defined.

#[global] Hint Resolve initial_is_terminal unique_iso_is_iso : core.

(* Equivalence of definitions *)

From Cat Require Limits.InitTerm.

Module Equiv.

#[refine]
#[export]
Instance hi_hieq (C : Cat) (hi : InitTerm.HasInit C) : HasInit C :=
{
  init := @InitTerm.init C hi;
  create := @InitTerm.create C hi;
}.
Proof. InitTerm.init. Defined.

#[refine]
#[export]
Instance hieq_hi (C : Cat) (hieq : HasInit C) : InitTerm.HasInit C :=
{
  InitTerm.init := @init C hieq;
  InitTerm.create := @create C hieq
}.
Proof. init. Defined.

#[refine]
#[export]
Instance ht_hteq (C : Cat) (ht : InitTerm.HasTerm C) : HasTerm C :=
{
  term := @InitTerm.term C ht;
  delete := @InitTerm.delete C ht;
}.
Proof. InitTerm.term. Defined.

#[refine]
#[export]
Instance hteq_ht (C : Cat) (hteq : HasTerm C) : InitTerm.HasTerm C :=
{
  InitTerm.term := @term C hteq;
  InitTerm.delete := @delete C hteq;
}.
Proof. intros. apply delete_unique. Defined.

End Equiv.

(* Duals *)

#[refine]
#[export]
Instance Dual_init_term (C : Cat) (hi : HasInit C) : HasTerm (Dual C) :=
{
  term := init C;
  delete := @create C hi
}.
Proof. init. init. cat. apply create_unique. Defined.

#[refine]
#[export]
Instance Dual_term_init (C : Cat) (ht : HasTerm C) : HasInit (Dual C) :=
{
  init := term C;
  create := @delete C ht
}.
Proof. cat. apply delete_unique. Defined.

#[refine]
#[export]
Instance Dual_HasZero (C : Cat) (hz : HasZero C) : HasZero (Dual C) :=
{
  zero_is_initial := @Dual_term_init C (@zero_is_terminal C hz);
  zero_is_terminal := @Dual_init_term C (@zero_is_initial C hz);
}.
Proof. cat. Defined.

(* Lemmas ported from InitTerm.v *)

Lemma HasInit_uiso :
  forall (C : Cat) (hi1 hi2 : HasInit C),
    @init C hi1 ~~ @init C hi2.
Proof.
  intros.
  red. exists (create (init C)). red. split.
    red. exists (create (init C)). split;
      rewrite create_unique, (create_unique (init C) (id (init C)));
        reflexivity.
    destruct hi1, hi2. intros. cbn. rewrite (create_unique0 _ y).
      cbn. reflexivity.
Qed.

Lemma HasTerm_uiso :
  forall (C : Cat) (ht1 ht2 : HasTerm C),
    @term C ht1 ~~ @term C ht2.
Proof.
  intros.
  red. exists (delete (term C)). red. split.
    red. exists (delete (term C)). split;
      rewrite delete_unique, (delete_unique (term C) (id (term C)));
        reflexivity.
    destruct ht1, ht2. intros. cbn. rewrite (delete_unique1 _ y).
      cbn. reflexivity.
Qed.

(*
Lemma iso_to_init_is_init :
  forall (C : Cat) (I X : Ob C) (create : forall I' : Ob C, Hom I I'),
    initial I create -> forall f : Hom X I, Iso f ->
      initial X (fun X' : Ob C => f .> create X').
Proof.
  repeat split; intros. iso.
  edestruct H. rewrite (H1 (f_inv .> y)). cat.
    assocl. rewrite f_inv_eq1. cat.
    trivial.
Defined.

Lemma iso_to_term_is_term : 
  forall (C : Cat) (X T : Ob C) (delete : forall T' : Ob C, Hom T' T),
    terminal T delete -> forall f : Hom T X, Iso f ->
      terminal X (fun X' : Ob C => delete X' .> f).
Proof.
  repeat split; intros. iso.
  edestruct H. rewrite (H1 (y .> f_inv)).
    assocr. rewrite f_inv_eq2. cat.
    trivial.
Defined.
*)

Lemma mor_to_init_is_ret :
  forall (C : Cat) (hi : HasInit C) (X : Ob C) (f : Hom X (init C)),
    Ret f.
Proof.
  intros. red. exists (create X).
  rewrite !create_unique.
  destruct hi. rewrite <- create_unique0. reflexivity.
Qed.

Lemma mor_from_term_is_sec :
  forall (C : Cat) (ht : HasTerm C) (X : Ob C) (f : Hom (term C) X),
    Sec f.
Proof.
  intros. red. exists (delete X).
  rewrite !delete_unique.
  destruct ht. rewrite <- delete_unique0. reflexivity.
Qed.