From Cat Require Export Cat.

Set Implicit Arguments.

Class isTerminal (C : Cat) (T : Ob C) (delete : forall X : Ob C, Hom X T) : Prop :=
  delete_equiv : forall {X : Ob C} (f g : Hom X T), f == g.

Arguments delete_equiv {C T delete isTerminal X f} _.

(* Class HasTerm' (C : Cat) (T : Ob C) : Type :=
{
  delete : forall X : Ob C, Hom X T;
  isTerminal_HasTerm' :> isTerminal C T delete;
}.

Arguments delete {C _ _} _.

Coercion isTerminal_HasTerm' : HasTerm' >-> isTerminal.

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  HasTerm'_HasTerm :> HasTerm' C term;
}.

Arguments term _ {_}.

Coercion HasTerm'_HasTerm : HasTerm >-> HasTerm'. *)

Class HasTerm (C : Cat) : Type :=
{
  term : Ob C;
  delete : forall X : Ob C, Hom X term;
  isTerminal_HasTerm' :> isTerminal C term delete;
}.

Arguments term   C {_}.
Arguments delete {C _} _.

Lemma isTerminal_uiso :
  forall
    (C : Cat)
    (T1 : Ob C) (delete1 : forall X : Ob C, Hom X T1)
    (T2 : Ob C) (delete2 : forall X : Ob C, Hom X T2),
      isTerminal C T1 delete1 ->
      isTerminal C T2 delete2 ->
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
      isTerminal C T1 delete1 ->
      isTerminal C T2 delete2 ->
        T1 ~ T2.
Proof.
  intros. destruct (isTerminal_uiso H H0). cat.
Qed.

Lemma isTerminal_delete_equiv :
  forall
    (C : Cat)
    (T : Ob C) (delete1 delete2 : forall X : Ob C, Hom X T),
      isTerminal C T delete1 ->
      isTerminal C T delete2 ->
        forall X : Ob C, delete1 X == delete2 X.
Proof.
  now intros; apply delete_equiv.
Qed.

Lemma iso_to_term_is_term :
  forall (C : Cat) (T : Ob C) (delete : forall X : Ob C, Hom X T),
    isTerminal C T delete ->
      forall {X : Ob C} (f : Hom T X), isIso f ->
        isTerminal C X (fun Y : Ob C => delete Y .> f).
Proof.
  intros C T d H X f (f' & Heq1 & Heq2) Y g1 g2.
  now rewrite <- comp_id_r, <- Heq2, <- comp_assoc, (delete_equiv (g2 .> f')),
    comp_assoc, Heq2, comp_id_r.
Defined.

Lemma mor_from_term_is_sec :
  forall (C : Cat) (T : Ob C) (delete : forall T' : Ob C, Hom T' T),
    isTerminal C T delete ->
      forall {X : Ob C} (f : Hom T X), isSec f.
Proof.
  unfold isSec; intros.
  exists (delete0 X).
  apply delete_equiv.
Qed.