From Cat Require Export Cat.
(* From Cat.Limits Require Import Initial. *)
Set Implicit Arguments.

Class isTerminal {C : Cat} (T : Ob C) (delete : forall X : Ob C, Hom X T) : Prop :=
  delete_equiv : forall {X : Ob C} (f g : Hom X T), f == g.

Arguments delete_equiv {C T delete isTerminal X f} _.

Class HasTerm' {C : Cat} (T : Ob C) : Type :=
{
  delete : forall X : Ob C, Hom X T;
  HasTerm'_isTerminal :> isTerminal T delete;
}.

Arguments delete {C _ _} _.

Coercion HasTerm'_isTerminal : HasTerm' >-> isTerminal.

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  HasTerm_HasTerm' :> HasTerm' term;
}.

Arguments term _ {_}.

Coercion HasTerm_HasTerm' : HasTerm >-> HasTerm'.

Lemma isTerminal_uiso :
  forall
    (C : Cat)
    (T1 : Ob C) (delete1 : forall X : Ob C, Hom X T1)
    (T2 : Ob C) (delete2 : forall X : Ob C, Hom X T2),
      isTerminal T1 delete1 ->
      isTerminal T2 delete2 ->
        T1 ~~ T2.
Proof.
  intros * H1 H2.
  exists (delete2 T1).
  repeat split.
  - exists (delete1 T2).
    split; apply delete_equiv.
  - now intros; apply delete_equiv.
Qed.

Lemma isTerminal_iso :
  forall
    (C : Cat)
    (T1 : Ob C) (delete1 : forall X : Ob C, Hom X T1)
    (T2 : Ob C) (delete2 : forall X : Ob C, Hom X T2),
      isTerminal T1 delete1 ->
      isTerminal T2 delete2 ->
        T1 ~ T2.
Proof.
  intros. destruct (isTerminal_uiso H H0). cat.
Qed.

Lemma isTerminal_delete_equiv :
  forall
    (C : Cat)
    (T : Ob C) (delete1 delete2 : forall X : Ob C, Hom X T),
      isTerminal T delete1 ->
      isTerminal T delete2 ->
        forall X : Ob C, delete1 X == delete2 X.
Proof.
  now intros; apply delete_equiv.
Qed.

Lemma iso_to_term_is_term :
  forall (C : Cat) (T : Ob C) (delete : forall X : Ob C, Hom X T),
    isTerminal T delete ->
      forall {X : Ob C} (f : Hom T X), isIso f ->
        isTerminal X (fun Y : Ob C => delete Y .> f).
Proof.
  intros C T d H X f (f' & Heq1 & Heq2) Y g1 g2.
  now rewrite <- comp_id_r, <- Heq2, <- comp_assoc, (delete_equiv (g2 .> f')),
    comp_assoc, Heq2, comp_id_r.
Defined.

Lemma mor_from_term_is_sec :
  forall (C : Cat) (T : Ob C) (delete : forall T' : Ob C, Hom T' T),
    isTerminal T delete ->
      forall {X : Ob C} (f : Hom T X), isSec f.
Proof.
  unfold isSec; intros.
  exists (delete0 X).
  apply delete_equiv.
Qed.