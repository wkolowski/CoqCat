Require Export Cat.
Require Export Cat.Functor.

Set Implicit Arguments.

Class has_init (C : Cat) : Type :=
{
    init : Ob C;
    create : forall X : Ob C, Hom init X;
    create_unique :
      forall (X : Ob C) (f : Hom init X), f == create X;
}.

Arguments init _ {has_init}.

Ltac init := intros; repeat
match goal with
    | |- context [?f] =>
        match type of f with
            | Hom (init _) _ => rewrite (create_unique _ f)
        end
    | |- ?x == ?x => reflexivity
end; try (cat; fail).

Class has_term (C : Cat) : Type :=
{
    term : Ob C;
    delete : forall X : Ob C, Hom X term;
    delete_unique :
      forall (X : Ob C) (f : Hom X term), f == delete X;
}.

Arguments term _ {has_term}.

Class has_zero (C : Cat) : Type :=
{
    zero_is_initial :> has_init C;
    zero_is_terminal :> has_term C;
    initial_is_terminal : init C = term C
}.

Coercion zero_is_initial : has_zero >-> has_init.
Coercion zero_is_terminal : has_zero >-> has_term.

Definition zero_ob (C : Cat) {hz : has_zero C} : Ob C := init C.
Definition zero_mor
  {C : Cat} {hz : has_zero C} (X Y : Ob C) : Hom X Y.
Proof.
  pose (f := delete X). pose (g := create Y).
  rewrite initial_is_terminal in g. exact (f .> g).
Defined.

Hint Resolve initial_is_terminal unique_iso_is_iso.

(* Equivalence of definitions *)

Module Equiv.

Require InitTerm.

#[refine]
Instance hi_hieq (C : Cat) (hi : InitTerm.has_init C) : has_init C :=
{
    init := @InitTerm.init C hi;
    create := @InitTerm.create C hi;
}.
Proof. InitTerm.init. Defined.

#[refine]
Instance hieq_hi (C : Cat) (hieq : has_init C) : InitTerm.has_init C :=
{
    InitTerm.init := @init C hieq;
    InitTerm.create := @create C hieq
}.
Proof. init. Defined.

#[refine]
Instance ht_hteq (C : Cat) (ht : InitTerm.has_term C) : has_term C :=
{
    term := @InitTerm.term C ht;
    delete := @InitTerm.delete C ht;
}.
Proof. InitTerm.term. Defined.

#[refine]
Instance hteq_ht (C : Cat) (hteq : has_term C) : InitTerm.has_term C :=
{
    InitTerm.term := @term C hteq;
    InitTerm.delete := @delete C hteq;
}.
Proof. intros. apply delete_unique. Defined.

End Equiv.

(* Duals *)

#[refine]
Instance Dual_init_term (C : Cat) (hi : has_init C) : has_term (Dual C) :=
{
    term := init C;
    delete := @create C hi
}.
Proof. init. init. cat. apply create_unique. Defined.

#[refine]
Instance Dual_term_init (C : Cat) (ht : has_term C) : has_init (Dual C) :=
{
    init := term C;
    create := @delete C ht
}.
Proof. cat. apply delete_unique. Defined.

#[refine]
Instance Dual_has_zero (C : Cat) (hz : has_zero C) : has_zero (Dual C) :=
{
    zero_is_initial := @Dual_term_init C (@zero_is_terminal C hz);
    zero_is_terminal := @Dual_init_term C (@zero_is_initial C hz);
}.
Proof. cat. Defined.

(* Lemmas ported from InitTerm.v *)

Lemma has_init_uiso :
  forall
    (C : Cat) (hi1 hi2 : has_init C),
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

(*
Lemma initial_create_equiv :
  forall
    (C : Cat) (hi1 hi2 : has_init C),
      @create C hi1 == @create C hi2.
*)

Lemma has_term_uiso :
  forall
    (C : Cat) (ht1 ht2 : has_term C),
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
Lemma terminal_delete_equiv :
  forall
    (C : Cat) (ht1 ht2 : has_term C),
      @delete C ht1 == @delete C ht2.
*)

(*
Lemma iso_to_init_is_init :
  forall (C : Cat) (I X : Ob C)
  (create : forall I' : Ob C, Hom I I'),
    initial I create -> forall f : Hom X I, Iso f ->
      initial X (fun X' : Ob C => f .> create X').
Proof.
  repeat split; intros. iso.
  edestruct H. rewrite (H1 (f_inv .> y)). cat.
    assocl. rewrite f_inv_eq1. cat.
    trivial.
Defined.

Lemma iso_to_term_is_term : 
  forall (C : Cat) (X T : Ob C)
  (delete : forall T' : Ob C, Hom T' T),
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
  forall
    (C : Cat) (hi : has_init C) (X : Ob C) (f : Hom X (init C)),
      Ret f.
Proof.
  intros. red. exists (create X).
  rewrite !create_unique.
  destruct hi. rewrite <- create_unique0. reflexivity.
Qed.

Lemma mor_from_term_is_sec :
  forall
    (C : Cat) (ht : has_term C) (X : Ob C) (f : Hom (term C) X),
      Sec f.
Proof.
  intros. red. exists (delete X).
  rewrite !delete_unique.
  destruct ht. rewrite <- delete_unique0. reflexivity.
Qed.

(*
Lemma mor_from_term_is_sec :
  forall (C : Cat) (T X : Ob C) (f : Hom T X)
  (delete : forall T' : Ob C, Hom T' T),
    terminal T delete -> Sec f.
Proof.
  intros. red. exists (delete0 X).
  edestruct H. rewrite <- H1; cat.
Qed.
*)